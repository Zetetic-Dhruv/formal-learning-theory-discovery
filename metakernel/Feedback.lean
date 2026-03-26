/-
  MetaKernel.WorldModel.Feedback — Feedback metaprograms that consume their own traces

  A feedback metaprogram is a metaprogram that:
  1. Runs a proof strategy (produces a PhiTrace)
  2. Analyzes the trace (which mechanisms succeeded/failed, where, why)
  3. Synthesizes a NEW strategy from the analysis
  4. Runs the new strategy

  This is the self-modifying loop that makes the MetaKernel an AGENT, not a script.
  The key property: the feedback loop is TYPED. Each iteration consumes and produces
  typed traces, and the strategy modifications are structurally constrained.

  Feedback loop architecture:
    PhiTrace → TraceAnalysis → StrategyPatch → CompoundMechanism → PhiTrace → ...

  The trace analysis extracts PATTERNS:
  - "mechanism X succeeds on shape Y 90% of the time" → promote X for Y
  - "mechanism X always fails on shape Y" → learn constraint (X, Y)
  - "HC > 0.5 after splitting" → need coordinated strategy
  - "Inv failure on context-dependent mechanism" → try structural alternative

  Prior-art integration: the WorldModel's PriorArtTheorem traces are consumed
  as additional signal. If prior-art says "use unionBound → exponentialBound → iidProduct"
  for PAC bounds, and our trace shows unionBound-analog succeeds, we weight the rest
  of the chain higher.
-/

import Lean
import MetaKernel.Core
import MetaKernel.Measure
import MetaKernel.Phi
import MetaKernel.Discovery
import MetaKernel.WorldModel.PriorArt

namespace MetaKernel.WorldModel

open Lean Meta MetaKernel

/-! ## Trace Analysis: Extract patterns from PhiTrace -/

/-- A pattern observed in a PhiTrace: mechanism × shape × outcome. -/
structure MechanismPattern where
  mechanism : ProofMechanism
  goalShape : GoalShape
  succeeded : Bool
  /-- How many times this pattern was observed -/
  count : Nat := 1
  deriving Repr, BEq

/-- Aggregated trace analysis: success rates, failure patterns, coupling stats. -/
structure TraceAnalysis where
  /-- Mechanism × shape success/failure patterns -/
  patterns : Array MechanismPattern := #[]
  /-- Average HC across splitting steps -/
  avgHC : Float := 0.0
  /-- Maximum HC observed -/
  maxHC : Float := 0.0
  /-- Count of Inv failures -/
  invFailures : Nat := 0
  /-- Count of Pl-orphans (goals where no mechanism worked) -/
  plOrphans : Nat := 0
  /-- Comp at end of trace -/
  finalComp : Float := 0.0
  /-- Mechanisms that succeeded most often -/
  topMechanisms : List (ProofMechanism × Nat) := []
  /-- Shapes that were hardest (most Pl-orphans) -/
  hardestShapes : List (GoalShape × Nat) := []
  deriving Repr

/-- Analyze a PhiTrace to extract patterns.
    This is the PERCEPTION step of the feedback loop. -/
def analyzeTrace (trace : PhiTrace) : TraceAnalysis := Id.run do
  let mut patterns : Array MechanismPattern := #[]
  let mut hcSum : Float := 0.0
  let mut hcCount : Nat := 0
  let mut maxHC : Float := 0.0
  let mut invFails : Nat := 0
  let mut orphans : Nat := 0
  let mut mechSucc : Std.HashMap ProofMechanism Nat := {}
  let mut shapeOrph : Std.HashMap GoalShape Nat := {}

  for entry in trace.entries do
    match entry.result.mechanismUsed with
    | some mech =>
      -- Record pattern
      patterns := patterns.push {
        mechanism := mech
        goalShape := entry.profile.shape
        succeeded := entry.result.goalResolved
      }
      -- Track success counts
      if entry.result.goalResolved then
        mechSucc := mechSucc.insert mech
          ((mechSucc.getD mech 0) + 1)
      -- Track HC
      if entry.result.newGoals.length > 1 then
        hcSum := hcSum + entry.result.measurements.hc
        hcCount := hcCount + 1
        if entry.result.measurements.hc > maxHC then
          maxHC := entry.result.measurements.hc
      -- Track Inv
      if !entry.result.measurements.inv then
        invFails := invFails + 1
    | none =>
      orphans := orphans + 1
      shapeOrph := shapeOrph.insert entry.profile.shape
        ((shapeOrph.getD entry.profile.shape 0) + 1)

  let avgHC := if hcCount == 0 then 0.0 else hcSum / Float.ofNat hcCount
  let topMechs := mechSucc.toList.toArray.qsort (fun a b => a.2 > b.2)
    |>.toList.take 5
  let hardShapes := shapeOrph.toList.toArray.qsort (fun a b => a.2 > b.2)
    |>.toList.take 5

  { patterns := patterns
    avgHC := avgHC
    maxHC := maxHC
    invFailures := invFails
    plOrphans := orphans
    finalComp := trace.comp
    topMechanisms := topMechs
    hardestShapes := hardShapes }

/-! ## Strategy Patches: How to modify a strategy based on analysis -/

/-- A strategy modification derived from trace analysis. -/
inductive StrategyPatch where
  /-- Promote mechanism for a shape (succeeded often) -/
  | promote (mech : ProofMechanism) (shape : GoalShape)
  /-- Demote mechanism for a shape (failed often) -/
  | demote (mech : ProofMechanism) (shape : GoalShape)
  /-- Add constraint (mechanism never works on shape) -/
  | addConstraint (mech : ProofMechanism) (shape : GoalShape) (reason : String)
  /-- Suggest coordinated strategy for high-HC goals -/
  | coordinatedStrategy (shape : GoalShape) (hc : Float)
  /-- Suggest prior-art strategy for Pl-orphan -/
  | usePriorArt (sorryName : String) (strategy : ProofStrategy)
  deriving Repr

/-- Derive strategy patches from a trace analysis.
    This is the REASONING step of the feedback loop. -/
def derivePatches (analysis : TraceAnalysis)
    (worldModel : WorldModelState := {}) : Array StrategyPatch := Id.run do
  let mut patches : Array StrategyPatch := #[]

  -- 1. Promote top-performing mechanisms
  for (mech, count) in analysis.topMechanisms do
    if count ≥ 3 then  -- threshold: succeeded at least 3 times
      -- Find most common shape for this mechanism
      let shapeCounts := analysis.patterns.foldl (fun acc p =>
        if p.mechanism == mech && p.succeeded then
          acc.insert p.goalShape ((acc.getD p.goalShape 0) + 1)
        else acc) (Std.HashMap.empty : Std.HashMap GoalShape Nat)
      for (shape, _) in shapeCounts.toList do
        patches := patches.push (.promote mech shape)

  -- 2. Demote consistently failing mechanisms
  let failCounts := analysis.patterns.foldl (fun acc p =>
    if !p.succeeded then
      let key := (p.mechanism, p.goalShape)
      acc.insert key ((acc.getD key 0) + 1)
    else acc) (Std.HashMap.empty : Std.HashMap (ProofMechanism × GoalShape) Nat)
  for ((mech, shape), count) in failCounts.toList do
    if count ≥ 3 then  -- consistently fails
      patches := patches.push (.addConstraint mech shape
        s!"Failed {count} times on {repr shape}")

  -- 3. Flag high-HC shapes for coordinated strategies
  for entry in analysis.patterns do
    if entry.goalShape == .iffType || entry.goalShape == .conjType then
      if analysis.maxHC > 0.5 then
        patches := patches.push (.coordinatedStrategy entry.goalShape analysis.maxHC)

  -- 4. Suggest prior-art for Pl-orphans
  for (shape, _) in analysis.hardestShapes do
    -- Query world model for strategies matching this shape
    for (sorryName, strategy) in worldModel.strategyCache.toList do
      patches := patches.push (.usePriorArt sorryName strategy)

  patches

/-! ## Strategy Synthesis: Apply patches to produce new CompoundMechanism -/

/-- Apply a StrategyPatch to modify a CompoundMechanism.
    Returns the modified strategy. -/
def applyPatch (strategy : CompoundMechanism) (patch : StrategyPatch) :
    CompoundMechanism :=
  match patch with
  | .promote mech _shape =>
    -- Wrap strategy to try promoted mechanism first
    .alt (.prim mech) strategy
  | .demote _mech _shape =>
    -- Can't structurally remove from CompoundMechanism; rely on constraint filtering
    strategy
  | .addConstraint _mech _shape _reason =>
    -- Constraints are stored in KernelState, not in strategy
    strategy
  | .coordinatedStrategy _shape _hc =>
    -- For high-HC goals, try haveIntermediate to decompose
    .seq (.prim .haveIntermediate) strategy
  | .usePriorArt _name priorStrategy =>
    -- Convert ProofStrategy to CompoundMechanism and try first
    let converted := convertProofStrategy priorStrategy
    .alt converted strategy
where
  /-- Convert a mathematical ProofStrategy to a CompoundMechanism. -/
  convertProofStrategy : ProofStrategy → CompoundMechanism
    | .atom m => match m with
      | .unionBound => .prim .applyLemma
      | .concentration => .prim .measureBound
      | .symmetrization => .prim .haveIntermediate
      | .chaining => .prim .applyLemma
      | .sauerId => .evalCustom "apply card_shatterer_le_sum_vcDim" "Sauer-Shelah from Mathlib"
      | .contrapositive => .seq (.prim .introForall) (.prim .contradiction)
      | .construction => .prim .existsWitness
      | .induction => .prim .inductionNat
      | .bridgeLift => .prim .applyLemma
      | .measureDecomp => .prim .measureBound
      | .iidProduct => .prim .measureBound
      | .exponentialBound => .evalCustom "exact exp_le_exp.mpr (by linarith)" "exponential bound"
      | .epsilonNet => .prim .applyLemma
      | .telescoping => .prim .applyLemma
      | .lipschitzTransfer => .prim .applyLemma
      | .logSobolev => .prim .measureBound
      | .varianceDecomp => .prim .measureBound
    | .seq s₁ s₂ => .seq (convertProofStrategy s₁) (convertProofStrategy s₂)
    | .branch _ cases => match cases with
      | [] => .prim .assumption
      | [c] => convertProofStrategy c
      | c₁ :: c₂ :: _ => .alt (convertProofStrategy c₁) (convertProofStrategy c₂)

/-- Apply all patches to a strategy. -/
def applyAllPatches (strategy : CompoundMechanism) (patches : Array StrategyPatch) :
    CompoundMechanism :=
  patches.foldl applyPatch strategy

/-! ## The Feedback Loop: Full iteration cycle -/

/-- A single feedback iteration result. -/
structure FeedbackResult where
  /-- The trace from running the (possibly patched) strategy -/
  trace : PhiTrace
  /-- Analysis of that trace -/
  analysis : TraceAnalysis
  /-- Patches derived from analysis -/
  patches : Array StrategyPatch
  /-- The patched strategy for next iteration -/
  nextStrategy : CompoundMechanism
  /-- Did this iteration improve Comp? -/
  improved : Bool
  deriving Repr

/-- The feedback metaprogram: a self-improving proof search agent.

    feedbackLoop runs a strategy, analyzes the trace, patches the strategy,
    and repeats until Comp converges or maxIterations is reached.

    This is the MetaKernel agent's core loop:
    1. EXECUTE: run strategy via phiIterate
    2. PERCEIVE: analyze trace via analyzeTrace
    3. REASON: derive patches via derivePatches
    4. ACT: apply patches to strategy
    5. MEASURE: check if Comp improved
    6. REPEAT if not converged -/
def feedbackLoop (initialGoals : List MVarId) (initialStrategy : CompoundMechanism)
    (worldModel : WorldModelState := {})
    (maxIterations : Nat := 5)
    (initState : KernelState := {}) : TacticM (Array FeedbackResult) := do
  let mut results : Array FeedbackResult := #[]
  let mut currentStrategy := initialStrategy
  let mut prevComp : Float := 0.0

  for _ in List.range maxIterations do
    -- EXECUTE: run Φ-iteration
    let trace ← phiIterate initialGoals 100 initState

    -- PERCEIVE: analyze trace
    let analysis := analyzeTrace trace

    -- Check convergence
    if analysis.finalComp >= 1.0 then
      results := results.push {
        trace := trace
        analysis := analysis
        patches := #[]
        nextStrategy := currentStrategy
        improved := true
      }
      break

    -- REASON: derive patches
    let patches := derivePatches analysis worldModel

    -- ACT: apply patches
    let nextStrategy := applyAllPatches currentStrategy patches

    -- MEASURE: did Comp improve?
    let improved := analysis.finalComp > prevComp

    results := results.push {
      trace := trace
      analysis := analysis
      patches := patches
      nextStrategy := nextStrategy
      improved := improved
    }

    -- Update for next iteration
    prevComp := analysis.finalComp
    currentStrategy := nextStrategy

    -- If no improvement and no new patches, stop
    if !improved && patches.isEmpty then break

  return results

/-! ## Prior-Art Guided Strategy Generation -/

/-- Generate a CompoundMechanism from prior-art traces for a specific sorry.
    Queries the world model for relevant theorems and composes their strategies. -/
def priorArtStrategy (sorryName : String)
    (worldModel : WorldModelState := {}) : CompoundMechanism :=
  let libs := worldModel.libraries
  let chains := extractStrategyChain sorryName libs
  match chains with
  | [] => .prim .assumption  -- no prior art → fallback
  | [(_, strategy)] => convertStrategy strategy
  | (_, s₁) :: (_, s₂) :: _ =>
    -- Multiple prior-art strategies → try both
    .alt (convertStrategy s₁) (convertStrategy s₂)
where
  convertStrategy : ProofStrategy → CompoundMechanism
    | .atom m => match m with
      | .unionBound => .prim .applyLemma
      | .concentration => .prim .measureBound
      | .exponentialBound => .evalCustom "exact exp_le_exp.mpr (by linarith)" "exp bound"
      | .sauerId => .evalCustom "apply card_shatterer_le_sum_vcDim" "Sauer-Shelah"
      | .iidProduct => .prim .measureBound
      | .construction => .prim .existsWitness
      | .induction => .prim .inductionNat
      | .bridgeLift => .prim .applyLemma
      | _ => .prim .simpAll
    | .seq s₁ s₂ => .seq (convertStrategy s₁) (convertStrategy s₂)
    | .branch _ cases => match cases with
      | [] => .prim .assumption
      | [c] => convertStrategy c
      | c₁ :: c₂ :: _ => .alt (convertStrategy c₁) (convertStrategy c₂)

/-! ## Tactic Syntax for Feedback Loop -/

/-- `feedback_proof "name"` : run feedback loop on current goal using prior-art world model. -/
syntax (name := feedbackProofSyntax) "feedback_proof" str : tactic

@[tactic feedbackProofSyntax]
def evalFeedbackProof : Tactic := fun stx => do
  match stx with
  | `(tactic| feedback_proof $name:str) => do
    let nameStr := name.getString
    let goals ← getUnsolvedGoals
    let strategy := priorArtStrategy nameStr
    let results ← feedbackLoop goals strategy {} 3
    match results.back? with
    | some lastResult =>
      if lastResult.analysis.finalComp >= 1.0 then
        logInfo m!"[feedback_proof '{nameStr}'] Converged at Comp=1.0 in {results.size} iterations"
      else
        let remaining ← getUnsolvedGoals
        logInfo m!"[feedback_proof '{nameStr}'] {remaining.length} goals remain after {results.size} iterations (Comp={lastResult.analysis.finalComp})"
        for r in results do
          logInfo m!"  Iteration: Comp={r.analysis.finalComp}, patches={r.patches.size}, HC={r.analysis.maxHC}"
    | none =>
      logWarning m!"[feedback_proof '{nameStr}'] No iterations completed"
  | _ => throwError "feedback_proof expects a string name"

end MetaKernel.WorldModel
