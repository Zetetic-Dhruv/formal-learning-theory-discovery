---
session: 10
date: 2026-03-31
title: "Interpolation of Concept Classes — Measurability Descent"
type: formalization-urs
status: awaiting-verification
target_file: FLT_Proofs/Complexity/Interpolation.lean
theorem_count: 8 (A-H)
sorry_budget: 0
M-type: M-Bridge
HC: 0.30
---

# Interpolation of Concept Classes — Measurability Descent

## Scientific Claim

If C₁ and C₂ are concept classes with Borel parameterizations (StandardBorelSpace
parameter spaces, jointly measurable evaluation maps), their **interpolation** — the
class of piecewise concepts agreeing with h₁ ∈ C₁ on region A and h₂ ∈ C₂ on Aᶜ —
satisfies `WellBehavedVCMeasTarget` (NullMeasurableSet bad events).

Prediction: composing well-behaved concept classes via ensemble methods preserves the
weaker measurability condition needed for PAC theory. The interpolated class may NOT
preserve KrappWirthWellBehaved (Borel-measurable ghost gap maps). Measurability
can only descend, not stay at the Borel level.

## Architecture

All interpolation theorems reduce to `patch_borel_param_wellBehavedVCMeasTarget`
(BorelAnalyticBridge.lean, sorry-free) via set-equality bridges. The new content is:
- Definitions (piecewiseConcept, interpClassFixed, interpClassCountable, interpClass)
- Router helpers (routerOfSet, routerOfSetFamily)
- Set-equality bridges showing interpClass* = range(patchEval ...)
- BorelRouterCode structure for the full conditional theorem
- Generic descent lemma

## File: `FLT_Proofs/Complexity/Interpolation.lean` (NEW)

### Imports

```lean
import FLT_Proofs.Complexity.BorelAnalyticBridge
```

This transitively imports Measurability.lean (for WellBehavedVCMeasTarget,
KrappWirthWellBehaved, oneSidedGhostGap, wellBehaved_event_eq_preimage_gapSup,
ghostGapSup, KrappWirthV).

## KK/KU/UK/UU Partition

| Quadrant | Content |
|----------|---------|
| **KK** | `patchEval` defined. `patch_borel_param_wellBehavedVCMeasTarget` proved sorry-free. `StandardBorelSpace` for `Unit`, `ℕ`, and products automatic in Mathlib. `Measurable.piecewise` in Mathlib. `wellBehaved_event_eq_preimage_gapSup` proved sorry-free. `KrappWirthV` = `Measurable (ghostGapSup C c m)`. |
| **KU** | (1) Does `Measurable.piecewise` accept `measurable_snd hA` directly for the indicator proof? Or does it need `MeasurableSet` on the product space, not the fiber? (2) For `routerOfSetFamily_measurable`, can we use `⋃ n, {n} ×ˢ A n` directly or does `MeasurableSet.iUnion` + `MeasurableSet.prod` need explicit `measurableSet_singleton (n : ℕ)`? (3) In `BorelRouterCode.surj_indicator`, should the surjectivity use `decide (x ∈ A)` (Bool-valued) or `x ∈ A` (Prop, coerced to Bool via `Decidable`)? (4) For the full equality theorem reverse direction: proving `{x \| R.eval ρ x = true}` is MeasurableSet from `R.eval_meas` — the route is `R.eval_meas.comp (measurable_const.prod_mk measurable_id) (measurableSet_singleton true)`. Does this compose correctly or does the `@Measurable` with explicit instances block it? |
| **UK** | The `if x ∈ A then ... else ...` in `piecewiseConcept` needs `Decidable (x ∈ A)` — may need `open Classical` or the `Set.piecewise` API instead of `if`. The `simp` closures in the set-equality bridges depend on how `patchEval`/`routerOfSet`/`piecewiseConcept` unfold — `decide_eq_true_eq` may or may not be the right simp lemma. |
| **UU** | Whether Lean4 elaboration will accept the `@patch_borel_param_wellBehavedVCMeasTarget` call with explicit `R.instMeasΡ` and `R.instStdΡ` instances, or whether it needs `letI` / `haveI` to put them in the instance cache. |

## Theorem Package

### Theorem A: `piecewiseConcept` definition (~5 LOC)

```lean
def piecewiseConcept {X : Type u} [MeasurableSpace X]
    (A : Set X) (h₁ h₂ : Concept X Bool) : Concept X Bool :=
  fun x => if x ∈ A then h₁ x else h₂ x
```

Needs `open Classical` for `Decidable (x ∈ A)`.

### Theorem B: `interpClassFixed`, `interpClassCountable`, `interpClass` (~15 LOC)

Three concept class definitions. Straightforward set-builder notation.

### Theorem C: `routerOfSet_measurable` (~8 LOC, HC 0.10)

```lean
theorem routerOfSet_measurable {A : Set X} (hA : MeasurableSet A) :
    Measurable (fun p : Unit × X => routerOfSet A p.1 p.2)
```

**Route**: `routerOfSet A () x = if x ∈ A then true else false` (after Classical).
This is `Set.indicator A (fun _ => true)` evaluated at `x`, composed with `Prod.snd`.
Use `Measurable.piecewise`:
- The set `{p : Unit × X | p.2 ∈ A}` = `Set.univ ×ˢ A`, which is `MeasurableSet.univ.prod hA`
  OR equivalently `measurable_snd hA`
- Both branches are `measurable_const`

**KU**: Does `Measurable.piecewise` expect `MeasurableSet {p | ...}` or
`MeasurableSet` on the second factor? Check the Mathlib signature:
```
Measurable.piecewise : MeasurableSet s → Measurable f → Measurable g →
    Measurable (Set.piecewise s f g)
```
So it needs `MeasurableSet {p : Unit × X | p.2 ∈ A}`, which is `measurable_snd hA`.

### Theorem D: `routerOfSetFamily_measurable` (~12 LOC, HC 0.15)

**Route**: `{p : ℕ × X | p.2 ∈ A p.1} = ⋃ n, {n} ×ˢ A n`.
- `ext ⟨n, x⟩; simp` should close the equality
- `MeasurableSet.iUnion (fun n => (measurableSet_singleton n).prod (hA n))` for the union
- Then `Measurable.piecewise` with `measurable_const` branches

### Theorem E: `interpClassFixed_eq_range_patchEval` (~12 LOC, HC 0.15)

**Route**: `ext h` then two directions:
- (→): extract `⟨θ₁, θ₂⟩`, build triple `(θ₁, θ₂, ())`, prove `ext x; simp`
- (←): extract `⟨θ₁, θ₂, _⟩`, build membership witnesses, prove `ext x; simp`

The `simp` needs to unfold `patchEval`, `routerOfSet`, `piecewiseConcept` and
resolve `decide`/`ite` equivalences. May need `decide_eq_true_eq` or
`Bool.decide_iff` or just `simp [patchEval, routerOfSet, piecewiseConcept]`.

### Theorem F: `interpClassCountable_eq_range_patchEval` (~12 LOC, HC 0.15)

Same pattern as E but with `ℕ` router and `routerOfSetFamily`.

### Theorem G: `interpClassFixed_wellBehaved` + `interpClassCountable_wellBehaved` (~10 LOC each, HC 0.10)

Both are one-liners after rewriting via E/F:
```lean
rw [interpClassFixed_eq_range_patchEval]
exact patch_borel_param_wellBehavedVCMeasTarget e₁ e₂ _ he₁ he₂ (routerOfSet_measurable hA)
```

### Theorem H: `not_KrappWirth_of_nonBorel_badEvent` (~10 LOC, HC 0.20)

**Route**:
1. Assume `hKW : KrappWirthWellBehaved X C`
2. Extract `hV : Measurable (ghostGapSup C c m)` from `hKW.V_measurable c m`
3. Rewrite bad event via `wellBehaved_event_eq_preimage_gapSup C c m ε hC`
4. Apply `hV measurableSet_Ici` to get `MeasurableSet` of the preimage
5. Contradicts `hbad`

**KU**: The signature of `wellBehaved_event_eq_preimage_gapSup` uses
`oneSidedGhostGap` in the set, NOT `EmpiricalError`. The theorem statement must
match: use `oneSidedGhostGap h c m p ≥ ε / 2` in the set definition, not the
raw `EmpiricalError` difference. They are definitionally equal but the `rw` will
only fire if the syntax matches.

### Full interpolation (BorelRouterCode conditional): ~40 LOC, HC 0.30

The `BorelRouterCode` structure and the conditional theorems
(`interpClass_eq_range_patchEval_of_routerCode`, `interpClass_wellBehaved_of_routerCode`).

**KU for the set-equality reverse direction**: Given `⟨θ₁, θ₂, ρ⟩`, need to produce
`A := {x | R.eval ρ x = true}` and show `MeasurableSet A`. Route:
- `R.eval ρ` is measurable as a function `X → Bool` because
  `R.eval_meas.comp (measurable_const.prod_mk measurable_id)` gives
  `Measurable (fun x => R.eval ρ x)`
- Then `MeasurableSet {x | R.eval ρ x = true}` is the preimage of `{true}` under
  this measurable function
- This needs the `@Measurable` instance annotation resolved correctly

**KU for `interpClass_wellBehaved_of_routerCode`**: The call to
`patch_borel_param_wellBehavedVCMeasTarget` needs `[MeasurableSpace R.Ρ]` and
`[StandardBorelSpace R.Ρ]` from the structure fields. May need `letI` / `haveI`:
```lean
letI := R.instMeasΡ
letI := R.instStdΡ
exact patch_borel_param_wellBehavedVCMeasTarget e₁ e₂ R.eval he₁ he₂ R.eval_meas
```

### Open question definition: `HasFullInterpolationRouterCode` (~3 LOC)

```lean
def HasFullInterpolationRouterCode (X : Type u) [MeasurableSpace X] : Prop :=
  Nonempty (BorelRouterCode X)
```

## Summary Table

| # | Theorem | LOC | HC | Route |
|---|---------|-----|-----|-------|
| A | piecewiseConcept def | 3 | 0.0 | Definition |
| B | interpClass* defs | 15 | 0.0 | Definitions |
| C | routerOfSet_measurable | 8 | 0.10 | Measurable.piecewise + measurable_snd |
| D | routerOfSetFamily_measurable | 12 | 0.15 | ⋃ n, {n} ×ˢ A n + Measurable.piecewise |
| E | interpClassFixed_eq_range_patchEval | 12 | 0.15 | ext + simp |
| F | interpClassCountable_eq_range_patchEval | 12 | 0.15 | ext + simp |
| G | Fixed + Countable wellBehaved | 20 | 0.10 | rw + patch_borel_param |
| H | not_KrappWirth_of_nonBorel_badEvent | 10 | 0.20 | wellBehaved_event_eq_preimage + V_meas |
| — | BorelRouterCode + conditional theorems | 40 | 0.30 | letI + ext + simp + patch_borel_param |
| — | HasFullInterpolationRouterCode | 3 | 0.0 | Definition |

Total: ~135 LOC, 0 sorrys.

## Agent Guardrails

When launching the agent:
1. `open Classical` at the top (needed for `Decidable (x ∈ A)` in piecewiseConcept)
2. A4-A5 checks before every proof
3. Must close ALL theorems sorry-free
4. Must not simplify or weaken any statement
5. NEVER run `git checkout`, `git restore`, or any working-tree discard command
6. The bad-event set in Theorem H must use `oneSidedGhostGap`, not raw `EmpiricalError`
7. For BorelRouterCode theorems, use `letI := R.instMeasΡ; letI := R.instStdΡ` to resolve instances
8. Build with `lake build FLT_Proofs.Complexity.Interpolation` after every major change
