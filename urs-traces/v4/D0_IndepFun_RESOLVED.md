# D0-IndepFun Research: iIndepFun_block_extract

## Status: PROOF STRATEGY IDENTIFIED — two viable routes

## The Sorry

File: `FLT_Proofs/Complexity/Generalization.lean.wip`, line 3273.

```lean
lemma iIndepFun_block_extract {X : Type*} [MeasurableSpace X]
    (k m : ℕ) (D : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure D] :
    ProbabilityTheory.iIndepFun (β := fun _ : Fin k => Fin m → X)
      (fun (j : Fin k) (ω : Fin (k * m) → X) => block_extract k m ω j)
      (MeasureTheory.Measure.pi (fun _ : Fin (k * m) => D)) := by
  sorry
```

Where `block_extract k m ω j = fun i => ω (finProdFinEquiv (j, i))`.

## Key Mathematical Insight

`block_extract k m ω j` is the `j`-th block of `ω`, obtained by currying
`ω ∘ finProdFinEquiv : Fin k × Fin m → X` and evaluating at `j`.

That is: `block_extract k m ω j = Function.curry (ω ∘ finProdFinEquiv) j`.

The map `e : (Fin (k*m) → X) → (Fin k → (Fin m → X))` defined by
`e ω j i = ω (finProdFinEquiv (j, i))` is a measurable equivalence that
sends `Measure.pi (fun _ : Fin (k*m) => D)` to
`Measure.pi (fun _ : Fin k => Measure.pi (fun _ : Fin m => D))`.

On the target space `Fin k → (Fin m → X)`, the functions `fun ω' => ω' j`
are just coordinate projections, and these are `iIndepFun` under the nested
product measure by `iIndepFun_pi`.

## Mathlib API Inventory

All in `.lake/packages/mathlib/Mathlib/Probability/Independence/`:

### Core definitions
- `iIndepFun` (Kernel/IndepFun.lean:47): `iIndep (m := fun x => comap (f x) (m x)) κ μ`
- `iIndepFun_iff_measure_inter_preimage_eq_mul` (Basic.lean:652): characterization via product formula
- `iIndepFun_iff_map_fun_eq_pi_map` (Basic.lean:706): characterization via pushforward = product of pushforwards

### Independence of projections
- `iIndepFun_pi` (Basic.lean:784): coordinate projections are `iIndepFun` under `Measure.pi`.
  Signature: `iIndepFun (fun i ω => X i (ω i)) (Measure.pi μ)` when `∀ i, AEMeasurable (X i) (μ i)`.
  With `X i = id`, gives: `iIndepFun (fun i ω => ω i) (Measure.pi μ)`.

### Composition
- `iIndepFun.comp` (Basic.lean:668): `iIndepFun f μ → (∀ i, Measurable (g i)) → iIndepFun (fun i => g i ∘ f i) μ`.
  Changes codomain, same index type.
- `iIndepFun.of_precomp` (Basic.lean:328): `g.Surjective → iIndepFun (fun i => f (g i)) μ → iIndepFun f μ`.
  Changes index type via surjection.

### Measure reindexing
- `measurePreserving_piCongrLeft` (Constructions/Pi.lean:744): reindexing a finite product measure.
- `measurePreserving_eval` (Constructions/Pi.lean:407): projection from product is measure-preserving (prob measures).
- `Measure.pi_map_pi` (Constructions/Pi.lean:390): `(pi μ).map (fun x i => f i (x i)) = pi (fun i => (μ i).map (f i))`.
- `Measure.pi_map_eval` (Constructions/Pi.lean:379): marginal of product measure.
- `infinitePi_eq_pi` (ProductMeasure.lean:509): `infinitePi μ = Measure.pi μ` for `Fintype ι`.
- `infinitePi_map_curry` (ProductMeasure.lean:557): currying for infinite product measures.

## Route A: Via `iIndepFun_iff_map_fun_eq_pi_map` (RECOMMENDED)

### Step 1: Prove AEMeasurability
Each `block_extract k m · j : (Fin (k*m) → X) → (Fin m → X)` is measurable
(it's a composition of measurable projections), hence AEMeasurable.

### Step 2: Compute the LHS
```
(Measure.pi (fun _ => D)).map (fun ω j => block_extract k m ω j)
```
The map `ω ↦ (fun j i => ω (finProdFinEquiv (j, i)))` is the composition:
1. `(MeasurableEquiv.piCongrLeft (fun _ => X) finProdFinEquiv).symm` : reindex `Fin (k*m) → X` to `Fin k × Fin m → X`
2. `MeasurableEquiv.curry (Fin k) (Fin m) X` : curry `Fin k × Fin m → X` to `Fin k → (Fin m → X)`

By `measurePreserving_piCongrLeft`, step 1 sends `Measure.pi (fun _ : Fin (k*m) => D)` to `Measure.pi (fun _ : Fin k × Fin m => D)`.

By `infinitePi_eq_pi` + `infinitePi_map_curry` (or direct computation via `pi_eq`), step 2 sends this to `Measure.pi (fun _ : Fin k => Measure.pi (fun _ : Fin m => D))`.

### Step 3: Compute the RHS
Each marginal: `(Measure.pi (fun _ => D)).map (block_extract k m · j)`.
This equals `Measure.pi (fun _ : Fin m => D)` because `block_extract · j` is
essentially projecting onto a sub-product and using `measurePreserving_piCongrLeft`.

Alternatively: rewrite via `pi_map_pi` by expressing block_extract as `eval j ∘ e`.

### Step 4: Conclude
Both sides equal `Measure.pi (fun _ : Fin k => Measure.pi (fun _ : Fin m => D))`.

### Proof sketch (tactic mode)
```lean
lemma iIndepFun_block_extract {X : Type*} [MeasurableSpace X]
    (k m : ℕ) (D : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure D] :
    ProbabilityTheory.iIndepFun (β := fun _ : Fin k => Fin m → X)
      (fun (j : Fin k) (ω : Fin (k * m) → X) => block_extract k m ω j)
      (MeasureTheory.Measure.pi (fun _ : Fin (k * m) => D)) := by
  -- The currying equiv
  let e : (Fin (k * m) → X) ≃ᵐ (Fin k → (Fin m → X)) :=
    (MeasurableEquiv.piCongrLeft (fun _ => X) finProdFinEquiv).symm.trans
      (MeasurableEquiv.curry (Fin k) (Fin m) X)
  -- Key: block_extract = eval ∘ e
  have he : ∀ j ω, block_extract k m ω j = e ω j := by
    intro j ω; ext i; simp [block_extract, e, MeasurableEquiv.piCongrLeft, MeasurableEquiv.curry]
  -- Rewrite using he
  simp_rw [he]
  -- Now the functions are (fun j ω => e ω j) = (fun j => (· j) ∘ e)
  -- Use iIndepFun_pi on the target product space:
  --   iIndepFun (fun j ω' => ω' j) (Measure.pi (fun _ => Measure.pi (fun _ => D)))
  -- Then transport via e being measure-preserving.
  sorry -- remaining glue
```

## Route B: Via `iIndepFun_iff_measure_inter_preimage_eq_mul` (DIRECT)

Work directly with the product formula. For each `S : Finset (Fin k)` and
measurable `sets j ⊆ (Fin m → X)`:

```
Measure.pi (fun _ => D) (⋂ j ∈ S, (block_extract k m · j) ⁻¹' sets j)
  = ∏ j ∈ S, Measure.pi (fun _ => D) ((block_extract k m · j) ⁻¹' sets j)
```

Each preimage `(block_extract k m · j) ⁻¹' sets j` depends only on
coordinates in block `j`. Since blocks are disjoint (`block_extract_disjoint`),
the intersection is a cylinder set in `Measure.pi`, and the product formula
follows from `Measure.pi_pi` applied to a suitable rectangle decomposition.

This route requires:
1. Express each `(block_extract · j) ⁻¹' (sets j)` as a cylinder set in `Measure.pi`.
2. Show the intersection of disjoint cylinder sets is again a cylinder set.
3. Apply `Measure.pi_pi` and simplify.

This is more elementary but requires more bookkeeping with pi-systems.

## Key Obstacle

Both routes require proving a **measure currying identity**:
```
(Measure.pi (fun _ : Fin (k*m) => D)).map (fun ω j i => ω (finProdFinEquiv (j, i)))
  = Measure.pi (fun _ : Fin k => Measure.pi (fun _ : Fin m => D))
```

This is NOT directly in Mathlib for `Measure.pi`. It exists for `infinitePi`
(`infinitePi_map_curry` in ProductMeasure.lean:557) and can be transported via
`infinitePi_eq_pi` (ProductMeasure.lean:509).

**Required additional import**: `Mathlib.Probability.ProductMeasure` (for `infinitePi_eq_pi`
and `infinitePi_map_curry`). This is NOT currently imported in Generalization.lean.

## Measurability

`block_extract k m · j` is measurable: it's a composition of `measurable_pi_lambda`
(constructing a function in a pi type from measurable components) where each
component `fun ω => ω (finProdFinEquiv (j, i))` is `measurable_pi_apply`.

Hence AEMeasurable (needed by `iIndepFun_iff_map_fun_eq_pi_map`).

## Action Items

1. Add `import Mathlib.Probability.ProductMeasure` to Generalization.lean.wip.
2. Implement Route A proof:
   a. Define the currying equiv `e`.
   b. Show `block_extract k m ω j = e ω j`.
   c. Prove the measure currying identity via `infinitePi_eq_pi` + `infinitePi_map_curry`.
   d. Apply `iIndepFun_pi` on the target and transport back.
3. Alternative: implement Route B if Route A has definitional unfolding issues.

## Estimated Difficulty

Medium-hard. The mathematical content is standard (product measure structure),
but the Lean4 formalization requires careful navigation of:
- `MeasurableEquiv.piCongrLeft` vs `MeasurableEquiv.curry` composition
- `Measure.pi` vs `infinitePi` bridge
- `finProdFinEquiv` definitional behavior
- Measurability of the currying equiv under `MeasurableSpace.pi`
