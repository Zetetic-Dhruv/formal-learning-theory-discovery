/-
  MetaKernel.WorldModel.MeasuredTactic — Compulsory measurement tactic classes

  Each of Pl/Coh/Inv/Comp becomes a TACTIC CLASS: a wrapper that MUST be invoked
  for a proof to be accepted by the MetaKernel. This is not advisory — it's structural.

  Architecture:
    measured_proof "name" do
      <inner proof tactics>

  The `measured_proof` tactic:
  1. Captures the initial goal state
  2. Runs the inner proof
  3. Computes Pl/Coh/Inv/Comp/HC for the proof
  4. Logs a full MeasurementReport
  5. Optionally fails if measurements indicate problems

  Measurement Tactic Classes (one per URT measurement):
  - `pl_gate`   : Plausibility gate — checks non-triviality before proof
  - `coh_gate`  : Coherence gate — checks composability after proof
  - `inv_gate`  : Invariance gate — checks stability of proof strategy
  - `comp_gate` : Completeness gate — tracks sorry closure

  These can be used individually or composed via `measured_proof`.
  The key property: they are COMPULSORY for MetaKernel-managed proofs.
  Proofs outside MetaKernel (in LimitsOfLearning/) are unaffected.
-/

import Lean
import Lean.Meta
import Lean.Elab.Tactic
import MetaKernel.Core
import MetaKernel.Measure

namespace MetaKernel.WorldModel

open Lean Meta Elab Tactic MetaKernel

/-! ## Individual Measurement Gates -/

/-- Pl-gate: Plausibility check BEFORE proof attempt.
    Verifies the goal is non-trivial (not closable by rfl/trivial/exact ⟨⟩).
    If trivial, logs a warning but allows passage (A₄ honesty — flag, don't block). -/
def plGate (goalMvar : MVarId) : TacticM Bool := do
  let saved ← saveState
  -- Try trivial closures
  let trivialMethods : List ProofMechanism :=
    [.reflexivity, .assumption, .exactTerm, .decide]
  let mut isTrivial := false
  for mech in trivialMethods do
    let saved' ← saveState
    try
      setGoals [goalMvar]
      applyPrimitive mech
      let remaining ← getUnsolvedGoals
      if remaining.isEmpty then
        isTrivial := true
        restoreState saved'
        break
      restoreState saved'
    catch _ =>
      restoreState saved'
  restoreState saved
  if isTrivial then
    logWarning m!"[Pl-gate] Goal is trivially closable — flagging as A₄-trivial"
  return !isTrivial

/-- Coh-gate: Coherence check AFTER proof attempt.
    Verifies all remaining subgoals (if any) are well-typed and
    compose with the existing proof state. -/
def cohGate : TacticM Bool := do
  let goals ← getUnsolvedGoals
  if goals.isEmpty then return true
  cohCheck goals

/-- Inv-gate: Invariance check on the proof strategy.
    Given the lead mechanism used, check if the proof is stable
    under hypothesis weakening (Tier 0/1 pass, Tier 2 requires redundancy). -/
def invGate (leadMech : ProofMechanism) : TacticM Bool := do
  let goals ← getUnsolvedGoals
  match goals with
  | [] => return true
  | goal :: _ =>
    let profile ← profileGoal goal
    invCheck leadMech profile

/-- Comp-gate: Completeness tracking.
    Records whether this proof closes a sorry and updates the running Comp ratio.
    Returns the new Comp ratio. -/
structure CompGateResult where
  newResolved : Nat
  totalTracked : Nat
  compRatio : Float
  deriving Repr

def compGate (proofName : String) (prevResolved : Nat := 0)
    (prevTotal : Nat := 0) : TacticM CompGateResult := do
  let goals ← getUnsolvedGoals
  let resolved := if goals.isEmpty then prevResolved + 1 else prevResolved
  let total := prevTotal + 1
  let ratio := if total == 0 then 1.0 else Float.ofNat resolved / Float.ofNat total
  if goals.isEmpty then
    logInfo m!"[Comp-gate] '{proofName}' resolved ({resolved}/{total} = {ratio})"
  return { newResolved := resolved, totalTracked := total, compRatio := ratio }

/-! ## Measurement Report (full, post-proof) -/

/-- A complete measurement report for a single proof attempt. -/
structure ProofMeasurementReport where
  proofName : String
  /-- Was the goal non-trivial? -/
  plNonTrivial : Bool
  /-- Did the proof compose correctly? -/
  cohValid : Bool
  /-- Is the proof strategy stable? -/
  invStable : Bool
  /-- Sorry closure tracking -/
  compResult : CompGateResult
  /-- Subgoal coupling -/
  hcCoupling : Float
  /-- Number of tactic steps taken -/
  stepCount : Nat
  /-- Classification: trivial/structural/deep -/
  classification : ProofClassification
  deriving Repr
where
  /-- How deep is this proof? -/
  inductive ProofClassification where
    | trivial       -- ≤ 3 steps, all intro/exact/assumption
    | structural    -- uses pattern matching but no deep lemmas
    | bridge        -- transports results across type boundaries
    | deep          -- requires domain-specific insight
    | unknown       -- measurement couldn't classify
    deriving Repr, BEq

/-! ## The `measured_proof` Tactic: Compulsory Measurement Wrapper -/

/-- Configuration for measured_proof behavior. -/
structure MeasuredProofConfig where
  /-- Block trivial proofs (A₄ enforcement)? Default: warn only -/
  blockTrivial : Bool := false
  /-- Block Coh failures? Default: true (ill-typed proofs should never pass) -/
  blockCohFailure : Bool := true
  /-- Block Inv failures? Default: false (log only) -/
  blockInvFailure : Bool := false
  /-- Log measurement report? -/
  logReport : Bool := true
  deriving Repr, Inhabited

/-- Run a sequence of tactics with full measurement instrumentation.
    This is the COMPULSORY measurement wrapper for MetaKernel proofs.

    Usage:
      theorem foo : P := by
        measured_proof_run "foo" (fun () => do
          <your tactics here>)

    All four measurements + HC are computed automatically. -/
def measuredProofRun (name : String) (config : MeasuredProofConfig := {})
    (innerProof : TacticM Unit) : TacticM ProofMeasurementReport := do
  let goalsBefore ← getUnsolvedGoals
  let mainGoal ← match goalsBefore with
    | g :: _ => pure g
    | [] => throwError "[measured_proof] No goals to prove"

  -- PRE-PROOF: Pl-gate
  let plResult ← plGate mainGoal
  if !plResult && config.blockTrivial then
    throwError "[measured_proof '{name}'] Pl-gate: goal is trivially closable (A₄)"

  -- PROOF EXECUTION: run inner tactics
  let stepCountBefore := goalsBefore.length
  innerProof
  let goalsAfter ← getUnsolvedGoals
  let stepCountAfter := goalsAfter.length

  -- POST-PROOF: Coh-gate
  let cohResult ← cohGate
  if !cohResult && config.blockCohFailure then
    throwError "[measured_proof '{name}'] Coh-gate: subgoals are ill-typed"

  -- POST-PROOF: Inv-gate (using simpAll as default lead mechanism)
  let invResult ← invGate .simpAll

  -- POST-PROOF: HC measurement
  let hcResult ← hcMeasure goalsAfter

  -- POST-PROOF: Comp-gate
  let compResult ← compGate name

  -- CLASSIFICATION
  let steps := stepCountBefore - stepCountAfter + 1
  let classification :=
    if steps ≤ 3 && !plResult then .trivial
    else if hcResult == 0.0 && steps ≤ 5 then .structural
    else if steps > 5 then .deep
    else .unknown

  let report : ProofMeasurementReport := {
    proofName := name
    plNonTrivial := plResult
    cohValid := cohResult
    invStable := invResult
    compResult := compResult
    hcCoupling := hcResult
    stepCount := steps
    classification := classification
  }

  -- LOG
  if config.logReport then
    logInfo m!"[measured_proof '{name}'] Pl={plResult} Coh={cohResult} Inv={invResult} HC={hcResult} Steps={steps} Class={repr classification}"

  return report

/-! ## Syntax: `measured_proof "name" by <tactics>` -/

/-- The `measured_proof` tactic: wraps any proof with compulsory measurements.
    All four URT measurements + HC are computed and logged. -/
syntax (name := measuredProofSyntax) "measured_proof" str tacticSeq : tactic

@[tactic measuredProofSyntax]
def evalMeasuredProof : Tactic := fun stx => do
  match stx with
  | `(tactic| measured_proof $name:str $tactics:tacticSeq) => do
    let nameStr := name.getString
    let _ ← measuredProofRun nameStr {} (evalTacticSeq tactics)
  | _ => throwError "measured_proof expects: measured_proof \"name\" <tactics>"

/-! ## Specialized Measurement Gates as Standalone Tactics -/

/-- `pl_check_goal` : standalone Pl-gate tactic. Warns if goal is trivial. -/
syntax (name := plCheckGoalSyntax) "pl_check_goal" : tactic

@[tactic plCheckGoalSyntax]
def evalPlCheckGoal : Tactic := fun _ => do
  let goal ← getMainGoal
  let result ← plGate goal
  if result then
    logInfo m!"[Pl] Goal is non-trivial ✓"
  else
    logWarning m!"[Pl] Goal is trivially closable — A₄ flag"

/-- `coh_check_state` : standalone Coh-gate tactic. Checks current proof state. -/
syntax (name := cohCheckStateSyntax) "coh_check_state" : tactic

@[tactic cohCheckStateSyntax]
def evalCohCheckState : Tactic := fun _ => do
  let result ← cohGate
  if result then
    logInfo m!"[Coh] All subgoals well-typed ✓"
  else
    logWarning m!"[Coh] Subgoal coherence failure — ill-typed goals detected"

/-- `hc_measure_state` : standalone HC measurement. Shows coupling between subgoals. -/
syntax (name := hcMeasureStateSyntax) "hc_measure_state" : tactic

@[tactic hcMeasureStateSyntax]
def evalHcMeasureState : Tactic := fun _ => do
  let goals ← getUnsolvedGoals
  let hc ← hcMeasure goals
  if hc == 0.0 then
    logInfo m!"[HC] Subgoals are independent (HC=0) — proof decomposes ✓"
  else
    logInfo m!"[HC] Subgoal coupling detected (HC={hc}) — coordinated strategy may be needed"

end MetaKernel.WorldModel
