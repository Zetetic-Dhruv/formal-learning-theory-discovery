---
session: 8
date: 2026-03-26
task_id: T3
target: map_block_extract_eq_pi
file: FLT_Proofs/Theorem/Separation.lean
status: closed
---

## T3: `map_block_extract_eq_pi` (line 430)

**File**: `FLT_Proofs/Theorem/Separation.lean`, line 430
**Scope**: Replace the `sorry` at line 430. Do not touch any other line.
**Dependencies**: None — uses only `iIndepFun_block_extract` internals from Generalization.lean and Mathlib product measure API.

### Current state (lines 422–430):

```lean
private lemma map_block_extract_eq_pi
    {X : Type u} [MeasurableSpace X]
    (k n : ℕ) (D : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure D] (j : Fin k) :
    (MeasureTheory.Measure.pi (fun _ : Fin (k * n) => D)).map
      (fun ω : Fin (k * n) → X => block_extract k n ω j)
      =
    MeasureTheory.Measure.pi (fun _ : Fin n => D) := by
  sorry
```

### What we need to show

The pushforward of `D^{k*n}` under `block_extract k n · j` (extracting the j-th block of n coordinates) equals `D^n`.

### Route

This is the marginal half of the `iIndepFun_block_extract` proof, pulled out as a standalone lemma. The key steps mirror Generalization.lean lines 2654–2707:

**Step 1**: Define the currying equivalence `e : (Fin (k*n) → X) ≃ᵐ (Fin k → Fin n → X)`:

```lean
  set pcl := MeasurableEquiv.piCongrLeft (fun _ : Fin k × Fin n => X) finProdFinEquiv.symm
  set cur := MeasurableEquiv.curry (Fin k) (Fin n) X
  set e : (Fin (k * n) → X) ≃ᵐ (Fin k → Fin n → X) := pcl.trans cur
```

**Step 2**: Show `block_extract k n ω j = e ω j`:

```lean
  have he : ∀ ω, block_extract k n ω j = e ω j := by
    intro ω; ext i
    simp [block_extract, e, pcl, cur, Function.curry,
      MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply]
```

**Step 3**: Compute `μ.map e` via measure-preserving equivalences:

```lean
  set μ := MeasureTheory.Measure.pi (fun _ : Fin (k * n) => D)
  set D' : Fin k → MeasureTheory.Measure (Fin n → X) :=
    fun _ => MeasureTheory.Measure.pi (fun _ : Fin n => D)

  have hpcl : MeasureTheory.MeasurePreserving pcl μ
      (MeasureTheory.Measure.pi (fun _ : Fin k × Fin n => D)) :=
    MeasureTheory.measurePreserving_piCongrLeft (fun _ => D) finProdFinEquiv.symm

  have hcur : (MeasureTheory.Measure.pi (fun _ : Fin k × Fin n => D)).map cur
      = MeasureTheory.Measure.pi D' := by
    -- infinitePi_map_curry or similar
    ...

  have hmap_e : μ.map e = MeasureTheory.Measure.pi D' := by
    have : (e : (Fin (k * n) → X) → (Fin k → Fin n → X)) = cur ∘ pcl := rfl
    rw [this, ← MeasureTheory.Measure.map_map cur.measurable pcl.measurable,
        hpcl.map_eq, hcur]
```

**Step 4**: Factor the map and use `measurePreserving_eval`:

```lean
  have hcomp : (fun ω => block_extract k n ω j) = (fun f => f j) ∘ e := by
    ext ω; exact he ω

  calc μ.map (fun ω => block_extract k n ω j)
      = μ.map ((fun f => f j) ∘ e) := by rw [hcomp]
    _ = (MeasureTheory.Measure.pi D').map (fun f => f j) := by
          rw [← MeasureTheory.Measure.map_map (measurable_pi_apply j) e.measurable, hmap_e]
    _ = D' j := (MeasureTheory.measurePreserving_eval D' j).map_eq
    _ = MeasureTheory.Measure.pi (fun _ : Fin n => D) := rfl
```

### The `hcur` step (Step 3)

This is the trickiest part. The route depends on which Mathlib API is available:

**Option A**: `MeasureTheory.infinitePi_map_curry` — if it exists, use:
```lean
  have hcur : ... := by
    rw [(MeasureTheory.infinitePi_eq_pi).symm]
    exact MeasureTheory.infinitePi_map_curry (fun _ : Fin k => fun _ : Fin n => D)
```

**Option B**: If `infinitePi_map_curry` doesn't exist, use `measurePreserving_sumPiEquivProdPi` composed with the currying equiv. This is the same route as `used_sample_split_measure` in Extended.lean (lines 471–497).

**Option C**: Use `MeasurableEquiv.map_apply` directly: since `cur` is a `MeasurableEquiv`, `μ.map cur = μ.map (cur : _ → _)` and we can show this equals `pi D'` by checking on measurable rectangles.

### Key Lean API

- `MeasurableEquiv.piCongrLeft` — reindex a pi type
- `MeasurableEquiv.curry` — `(α × β → γ) ≃ᵐ (α → β → γ)`
- `MeasureTheory.measurePreserving_piCongrLeft` — reindexing preserves pi measure
- `MeasureTheory.measurePreserving_eval` — projection from pi measure gives the factor
- `MeasureTheory.Measure.map_map` — `(g ∘ f)_* μ = g_*(f_* μ)`
- `finProdFinEquiv` — `Fin k × Fin n ≃ Fin (k * n)`

### Reference

The proof of `iIndepFun_block_extract` in Generalization.lean (lines 2654–2707) contains all these steps. The `e`, `pcl`, `cur`, `hpcl`, `hcur`, `hmap_e` setup is already there. This lemma just extracts the marginal identity from that proof.

### Estimated LOC: ~30

### Guardrails
- A4/A5 checks
- No new sorry
- Edit only line 430
- Do not touch any other lemma
- NEVER run `git checkout`, `git restore`, or any working-tree discard command