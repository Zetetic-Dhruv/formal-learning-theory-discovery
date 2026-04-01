---
session: 10
date: 2026-04-02
title: "Proof Operad Phase 4: Bridge Tactic + Four-Gate Quality Model"
type: formalization-urs
status: awaiting-verification
target_file: FLT_Proofs/Meta/BridgeTactic.lean (NEW)
theorem_count: 2 soundness lemmas
sorry_budget: 0
M-type: M-Construction (operational tactic)
HC: 0.45
---

# Proof Operad Phase 4: Bridge Tactic + Four-Gate Quality Model

## Deliverable

A Lean4 tactic `bridge_search` that, given a proof goal:

1. **Classifies** the goal by paradigm (PAC/Online/Gold/DST/Bayes) via type-family
   pattern matching on the target `Expr`
2. **Searches** the environment for lemmas whose conclusion unifies with the goal
   AND whose hypotheses are satisfiable from the local context
3. **Filters** by admissibility (paradigm lock, premise check) using the operad's
   failure rules
4. **If found**: applies the lemma, closing or reducing the goal
5. **If not found**: produces a structured `BridgeReport` classifying the gap as
   bridge (precise, one lemma away) or open-ended (diffuse, needs new strategy)

This is the operational form of the proof operad: the theory EXECUTES.

## Lean4 Metaprogramming Substrate

From the book (Chapters 4, 7, 8):

```
-- Goal inspection
MVarId.getType : MVarId → MetaM Expr           -- get target type
MVarId.getDecl : MVarId → MetaM MetavarDecl     -- get full declaration
MVarId.withContext : MVarId → MetaM α → MetaM α -- run in goal's context
getLCtx : MetaM LocalContext                     -- local hypotheses

-- Expression analysis
Expr.isApp, Expr.getAppFn, Expr.getAppArgs      -- deconstruct applications
Expr.isConst, Expr.constName!                    -- identify constants
isDefEq : Expr → Expr → MetaM Bool              -- unification

-- Environment search
getEnv : CoreM Environment                       -- all declarations
Environment.constants : Environment → ConstantMap
ConstantInfo.type : ConstantInfo → Expr          -- get a declaration's type

-- Tactic operations
getMainGoal : TacticM MVarId                     -- current goal
replaceMainGoal : List MVarId → TacticM Unit     -- set new goals
closeMainGoalUsing : (Expr → MetaM Expr) → TacticM Unit

-- Backtracking
saveState : MetaM SavedState
restoreState : SavedState → MetaM Unit
observing? : MetaM α → MetaM (Option α)
```

## File: `FLT_Proofs/Meta/BridgeTactic.lean` (NEW)

### Imports

```lean
import FLT_Proofs.Meta.ProofOperadInstances
import Lean.Elab.Tactic.Basic
import Lean.Meta.Basic
```

This file bridges the pure theory (ProofOperad) with Lean4's metaprogramming runtime.

---

## Part 1: Four-Gate Step Quality (~20 LOC)

```lean
/-- The four binary quality gates from the First Proof Benchmark.
    Each proof step is scored on all four independently. -/
structure StepQuality where
  /-- Step stays within the interface's stated premises -/
  assumptionCompliance : Bool
  /-- The mathematical content of the step is correct -/
  inferenceValidity : Bool
  /-- The local objective (output interface) is achieved -/
  goalCompletion : Bool
  /-- The step survives transport to wider interfaces -/
  generalizationRobustness : Bool
  deriving Repr, DecidableEq, BEq
```

```lean
/-- The quality funnel: compliance ≥ validity ≥ completion ≥ robustness.
    This is the empirical finding: rates are monotonically decreasing. -/
def StepQuality.funnelValid (q : StepQuality) : Bool :=
  (!q.inferenceValidity || q.assumptionCompliance) &&
  (!q.goalCompletion || q.inferenceValidity) &&
  (!q.generalizationRobustness || q.goalCompletion)
```

---

## Part 2: Gap Classification (~20 LOC)

```lean
/-- Two types of gaps, distinguished by the benchmark's empirical finding:
    bridge failures are tractable, open-ended failures are not. -/
inductive GapType where
  /-- Precise gap: single missing lemma connecting two known results.
      The benchmark finds these convert at higher rates (P1, P7). -/
  | bridge (source target : String) (missingLemma : String)
  /-- Diffuse gap: no clear bridge, needs new proof strategy.
      The benchmark finds these rarely convert (P3, P4). -/
  | openEnded (reason : String)
  deriving Repr
```

```lean
/-- A bridge report: the structured output when a goal can't be closed.
    This is the operational form of GapSpec + quality assessment. -/
structure BridgeReport where
  /-- The paradigm of the goal -/
  paradigm : Paradigm
  /-- The gap classification -/
  gapType : GapType
  /-- The quality assessment of the search attempt -/
  quality : StepQuality
  /-- Names of lemmas that were tried and failed -/
  triedAndFailed : List String
  /-- The goal's target type as a string (for reporting) -/
  goalDescription : String
  deriving Repr
```

---

## Part 3: Interface Widening + Robustness (~15 LOC)

```lean
/-- Interface I' is a widening of I: fewer premises, broader scope. -/
def Interface.widens (I I' : Interface) : Bool :=
  I'.premises.all (fun p => I.premises.contains p) &&
  I'.locks.all (fun l => I.locks.contains l)

/-- A generator application is robust if it remains admissible under widening. -/
def Generator.isRobust (Sigma : Theory) (g : Generator) (I : Interface) : Bool :=
  -- Check: would admissibility hold if we removed each premise one at a time?
  I.premises.all fun p =>
    let I' := { I with premises := I.premises.filter (· != p) }
    match Sigma.admissible I' g with
    | .ok () => true
    | .error _ => false
```

---

## Part 4: Paradigm Classifier (~30 LOC)

The core of the tactic: inspect an `Expr` and determine which paradigm it lives in.

```lean
open Lean Meta Elab Tactic in

/-- Classify a goal's target expression by paradigm.
    Pattern-matches on the head constant of the target type. -/
def classifyExpr (e : Expr) : MetaM Paradigm := do
  let e ← whnf e  -- reduce to head normal form
  let head := e.getAppFn
  if head.isConst then
    let name := head.constName!
    -- PAC paradigm: measure theory types
    if name.toString.containsSubstr "Measure"
       || name.toString.containsSubstr "ENNReal"
       || name.toString.containsSubstr "PACLearnable"
       || name.toString.containsSubstr "EmpiricalError"
       || name.toString.containsSubstr "WellBehavedVC" then
      return .pac
    -- Online paradigm
    if name.toString.containsSubstr "OnlineLearner"
       || name.toString.containsSubstr "LittlestoneDim"
       || name.toString.containsSubstr "LTree"
       || name.toString.containsSubstr "versionSpace" then
      return .online
    -- Gold paradigm
    if name.toString.containsSubstr "DataStream"
       || name.toString.containsSubstr "MindChange"
       || name.toString.containsSubstr "EXLearnable" then
      return .gold
    -- DST paradigm
    if name.toString.containsSubstr "AnalyticSet"
       || name.toString.containsSubstr "NullMeasurable"
       || name.toString.containsSubstr "PolishSpace"
       || name.toString.containsSubstr "StandardBorel" then
      return .dst
    -- Bayes paradigm
    if name.toString.containsSubstr "FinitePMF"
       || name.toString.containsSubstr "klDiv" then
      return .bayes
    -- Separation paradigm
    if name.toString.containsSubstr "KrappWirth"
       || name.toString.containsSubstr "WellBehavedVCMeasTarget" then
      return .separation
  return .structural  -- default: no paradigm lock detected
```

---

## Part 5: Bridge Lemma Search (~50 LOC)

The search algorithm:
1. Get the goal's target type
2. Classify by paradigm
3. Search the environment for constants whose type is a Pi-type
   ending in something that unifies with the target
4. For each candidate, check if the hypotheses can be satisfied
   from the local context
5. Return the first match, or a BridgeReport if none found

```lean
open Lean Meta Elab Tactic in

/-- Search for a lemma in the environment whose conclusion unifies
    with the given target, and whose hypotheses are satisfiable
    from the local context. Returns the lemma name if found. -/
def searchBridgeLemma (goal : MVarId) (paradigm : Paradigm) :
    MetaM (Option Name) := do
  let target ← goal.getType
  let env ← getEnv
  let lctx ← getLCtx
  -- Collect candidate lemma names from the environment
  let mut candidates : Array Name := #[]
  for (name, info) in env.constants.map₁.toList do
    -- Skip internal names
    if name.isInternal then continue
    -- Quick filter: only look at theorems (not defs, axioms)
    match info with
    | .thmInfo _ =>
      -- Try to unify the conclusion with our target
      let saved ← saveState
      let result ← observing? do
        let lemmaType := info.type
        -- Open the forall telescope to get the conclusion
        forallTelescopeReducing lemmaType fun args conclusion => do
          -- Check if conclusion unifies with target
          if ← isDefEq conclusion target then
            -- Check if all arguments can be synthesized or found in context
            let mut allSatisfied := true
            for arg in args do
              let argType ← inferType arg
              -- Try to find a matching hypothesis
              let found ← lctx.anyM fun decl => do
                if decl.isImplementationDetail then return false
                isDefEq decl.type argType
              unless found do
                -- Try instance synthesis
                let inst? ← observing? (synthInstance argType)
                unless inst?.isSome do
                  allSatisfied := false
            if allSatisfied then
              return name
            else
              throwError "not all hypotheses satisfiable"
      restoreState saved
      if let some foundName := result then
        candidates := candidates.push foundName
    | _ => continue
  -- Return first candidate (if any)
  if h : candidates.size > 0 then
    return some candidates[0]
  else
    return none
```

**IMPORTANT NOTE**: This is a SKETCH. The full environment search is expensive
(thousands of constants). In practice, we should:
- Pre-filter by paradigm (only search PAC lemmas for PAC goals)
- Limit search depth (only look at lemmas in FLT_Proofs namespace)
- Cache results

For Phase 4, the search is LIMITED to the current file's namespace
(`FLT_Proofs`), not the full Mathlib. This keeps it tractable.

```lean
/-- Restricted search: only look in FLT_Proofs namespace. -/
def searchBridgeLemmaRestricted (goal : MVarId) (paradigm : Paradigm) :
    MetaM (Option Name) := do
  let target ← goal.getType
  let env ← getEnv
  let mut result : Option Name := none
  for (name, info) in env.constants.map₁.toList do
    if name.isInternal then continue
    unless name.toString.startsWith "FLT_Proofs" || name.toString.startsWith "flt" do continue
    match info with
    | .thmInfo _ =>
      let saved ← saveState
      let found ← observing? do
        forallTelescopeReducing info.type fun _ conclusion => do
          if ← isDefEq conclusion target then return name
          else throwError "no match"
      restoreState saved
      if let some n := found then
        result := some n
        break
    | _ => continue
  return result
```

---

## Part 6: The Bridge Tactic (~30 LOC)

```lean
open Lean Meta Elab Tactic in

/-- `bridge_search` tactic: search for a bridge lemma that closes the current goal.
    If found, apply it. If not, report a structured BridgeReport to the info view. -/
elab "bridge_search" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let target ← goal.getType
    let paradigm ← classifyExpr target
    -- Search for a bridge lemma
    let result ← searchBridgeLemmaRestricted goal paradigm
    match result with
    | some name =>
      -- Found a bridge lemma — apply it
      let lemmaExpr := mkConst name
      let newGoals ← goal.apply lemmaExpr
      replaceMainGoal newGoals.toList
      logInfo m!"bridge_search: applied {name}"
    | none =>
      -- No bridge found — report structured gap
      let goalStr := toString (← ppExpr target)
      let report : BridgeReport := {
        paradigm := paradigm
        gapType := .bridge (toString paradigm) goalStr "unknown"
        quality := ⟨true, true, false, false⟩  -- compliance + validity OK, completion + robustness fail
        triedAndFailed := []
        goalDescription := goalStr
      }
      logWarning m!"bridge_search: no bridge found.\n{repr report}"
      -- Leave goal open — the report IS the output
```

---

## Part 7: Soundness (~20 LOC)

```lean
/-- Bridge failure implies a gap exists in the operad theory. -/
theorem bridge_failure_implies_gap
    (Sigma : Theory) (I : Interface)
    (report : BridgeReport)
    (hfail : report.quality.goalCompletion = false) :
    ∃ gap : GapSpec, gap.source = I := by
  exact ⟨⟨I, ⟨"bridge_target", I.locks, I.premises, "bridge_target"⟩,
          .missingBridge I.name "bridge_target"⟩, rfl⟩

/-- The quality funnel is respected: robustness ≤ completion ≤ validity ≤ compliance. -/
theorem quality_funnel_monotone (q : StepQuality) (h : q.funnelValid = true) :
    (q.generalizationRobustness → q.goalCompletion) ∧
    (q.goalCompletion → q.inferenceValidity) ∧
    (q.inferenceValidity → q.assumptionCompliance) := by
  simp [StepQuality.funnelValid] at h
  constructor
  · intro hr; by_contra hc; simp_all
  constructor
  · intro hg; by_contra hv; simp_all
  · intro hv; by_contra ha; simp_all
```

---

## KK/KU/UK/UU

| Quadrant | Content |
|----------|---------|
| **KK** | Lean4's `elab` syntax for custom tactics. `MVarId.apply` for lemma application. `forallTelescopeReducing` for opening binders. `observing?` for backtracking. `logInfo`/`logWarning` for tactic output. |
| **KU** | (1) Does `env.constants.map₁.toList` give access to all declarations? Or is it `env.constants.fold`? The exact API for iterating over the environment may differ. (2) Does `MVarId.apply` handle implicit arguments automatically? Yes — it creates fresh metavariables for them. (3) Can `String.containsSubstr` be used on `Name.toString`? Need to check if this is available or if we need `String.isSubstrOf`. |
| **UK** | The full environment search is O(n) in the number of declarations. For the FLT kernel this is ~200 defs + ~280 theorems = tractable. For Mathlib it would be ~200K — need the namespace restriction. |
| **UU** | Whether `isDefEq` with metavariable assignment during the search will cause side effects that corrupt the goal state. The `saveState`/`restoreState` bracketing should prevent this, but the book warns that caches are not restored. |

---

## Execution Plan

| Phase | Action | LOC |
|-------|--------|-----|
| 4a | StepQuality + funnelValid + quality_funnel_monotone | ~25 |
| 4b | GapType + BridgeReport | ~20 |
| 4c | Interface.widens + Generator.isRobust | ~15 |
| 4d | classifyExpr (paradigm classifier) | ~30 |
| 4e | searchBridgeLemmaRestricted | ~30 |
| 4f | bridge_search tactic | ~25 |
| 4g | bridge_failure_implies_gap | ~10 |
| 4h | Build + test on a simple goal | ~5 |

Total: ~160 LOC.

---

## Agent Guardrails

1. NEVER run `git checkout`, `git restore`, or any working-tree discard
2. Build after every phase (4a through 4h)
3. Zero sorrys
4. Import `FLT_Proofs.Meta.ProofOperadInstances` AND Lean metaprogramming:
   `import Lean.Elab.Tactic.Basic` and `import Lean.Meta.Basic`
5. Do NOT modify any existing file
6. The `classifyExpr` function should use `Name.toString` and string matching —
   do NOT try to resolve actual Lean `Name` constants from the FLT_Proofs namespace
   (that would create import cycles)
7. The `searchBridgeLemmaRestricted` MUST use `saveState`/`restoreState` around
   every `isDefEq` call to prevent metavariable pollution
8. The `bridge_search` tactic should work on ANY goal — it degrades gracefully
   (reports a gap) rather than failing with an error
9. If the environment iteration API doesn't match the URS sketch, adapt —
   the BEHAVIOR (search + classify + report) is fixed, the API calls may vary
10. Test the tactic on at least one concrete goal by writing:
    ```lean
    example : True := by bridge_search  -- should report: no bridge found
    ```
