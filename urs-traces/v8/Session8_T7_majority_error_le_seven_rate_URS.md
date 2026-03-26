---
session: 8
date: 2026-03-26
task_id: T7
target: majority_error_le_seven_rate_of_good_fraction
file: FLT_Proofs/Theorem/Separation.lean
status: closed
---

## T7: `majority_error_le_seven_rate_of_good_fraction` (line 706)

**File**: `FLT_Proofs/Theorem/Separation.lean`, line 706
**Scope**: Replace the `sorry` at line 706. Do not touch any other line.
**Dependencies**: None — standalone deterministic lemma.

### Current state (lines 689–706):

```lean
private lemma majority_error_le_seven_rate_of_good_fraction
    {X : Type u} [MeasurableSpace X]
    (D : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure D]
    {k : ℕ} (hk_pos : 0 < k)
    (c : Concept X Bool) (hc_meas : Measurable c)
    (hs : Fin k → Concept X Bool)
    (hhs_meas : ∀ j : Fin k, Measurable (hs j))
    (good : Finset (Fin k))
    (hgoodfrac : 7 * k ≤ 12 * good.card)
    (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hgooderr : ∀ j ∈ good, D {x : X | hs j x ≠ c x} ≤ ENNReal.ofReal ρ) :
    D {x : X | boosted_majority k (fun j => hs j x) ≠ c x}
      ≤ ENNReal.ofReal (7 * ρ) := by
  sorry
```

### Verbatim working proof (extracted from previous agent JSONL)

This is the exact proof that compiled successfully. Drop it in replacing `sorry`:

```lean
  classical
  let bad : Fin k → Set X := fun j => {x : X | hs j x ≠ c x}
  have hbad_meas : ∀ j, MeasurableSet (bad j) := by
    intro j
    have : {x : X | hs j x ≠ c x} = {x : X | hs j x = c x}ᶜ := by
      ext x; simp [ne_eq, Set.mem_compl_iff, Set.mem_setOf_eq]
    rw [this]
    exact (measurableSet_eq_fun (hhs_meas j) hc_meas).compl
  -- G(x) = Σ_{j ∈ good} 2 · 𝟙[hs j x ≠ c x], as ENNReal
  let G : X → ENNReal := fun x =>
    ∑ j ∈ good, (bad j).indicator (fun _ => (2 : ENNReal)) x
  have hG_meas : Measurable G := by
    refine Finset.measurable_sum good ?_
    intro j _
    exact Measurable.indicator measurable_const (hbad_meas j)
  have hG_ae : AEMeasurable G D := hG_meas.aemeasurable
  -- Subset inclusion: {majority wrong} ⊆ {G(x) ≥ threshold}
  let threshold : ENNReal := (2 * good.card - k : ℕ)
  have hklt : k < 2 * good.card := by
    have : (7 : ℕ) * k ≤ 12 * good.card := hgoodfrac
    omega
  have hden_pos_nat : 0 < 2 * good.card - k := Nat.sub_pos_of_lt hklt
  have hmajority_sub :
      {x : X | boosted_majority k (fun j => hs j x) ≠ c x}
        ⊆ {x : X | threshold ≤ G x} := by
    intro x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    -- Count wrong hypotheses
    set wrongAll : ℕ := (Finset.univ.filter (fun j => hs j x ≠ c x)).card with hwrongAll_def
    set wrongGood : ℕ := (good.filter (fun j => hs j x ≠ c x)).card with hwrongGood_def
    -- Majority wrong ⟹ k ≤ 2 * wrongAll
    have hwrong_all : k ≤ 2 * wrongAll := by
      simp only [boosted_majority] at hx
      by_cases hcx : c x = true
      · have hmaj_false : ¬(k < 2 * (Finset.univ.filter fun j => hs j x).card) := by
          by_contra h
          simp [hcx, h] at hx
        have hfilt_eq : (Finset.univ.filter (fun j : Fin k => hs j x ≠ c x))
            = (Finset.univ.filter (fun j : Fin k => hs j x = false)) := by
          ext j; simp [hcx]
        have hcomp := Finset.filter_card_add_filter_neg_card_eq_card
          (Finset.univ : Finset (Fin k)) (fun j => hs j x = true)
        simp only [Finset.card_univ, Fintype.card_fin] at hcomp
        have hfilt_true : (Finset.univ.filter fun j : Fin k => hs j x).card
            = (Finset.univ.filter fun j : Fin k => hs j x = true).card := by
          congr 1; ext j; simp
        have hfilt_false : (Finset.univ.filter (fun j : Fin k => ¬hs j x = true)).card
            = (Finset.univ.filter (fun j : Fin k => hs j x = false)).card := by
          congr 1; ext j; simp [Bool.not_eq_true]
        rw [hfilt_eq]
        omega
      · push_neg at hcx
        simp only [Bool.not_eq_true] at hcx
        have hcx_false : c x = false := by cases c x <;> simp_all
        have hmaj_true : k < 2 * (Finset.univ.filter fun j => hs j x).card := by
          by_contra h
          push_neg at h
          simp [hcx_false, Nat.not_lt.mpr h] at hx
        have hfilt_eq : (Finset.univ.filter (fun j : Fin k => hs j x ≠ c x))
            = (Finset.univ.filter (fun j : Fin k => hs j x = true)) := by
          ext j; simp [hcx_false]
        have hfilt_true : (Finset.univ.filter fun j : Fin k => hs j x).card
            = (Finset.univ.filter fun j : Fin k => hs j x = true).card := by
          congr 1; ext j; simp
        rw [hfilt_eq]
        omega
    -- wrongAll ≤ wrongGood + (k - good.card)
    have hwrong_split : wrongAll ≤ wrongGood + (k - good.card) := by
      have hpart := Finset.filter_card_add_filter_neg_card_eq_card
        (Finset.univ.filter (fun j : Fin k => hs j x ≠ c x)) (fun j => j ∈ good)
      have hgood_in : (Finset.univ.filter (fun j : Fin k => hs j x ≠ c x) |>.filter
          (fun j => j ∈ good)).card = wrongGood := by
        congr 1; ext j; simp [Finset.mem_filter]
      have hbad_le : (Finset.univ.filter (fun j : Fin k => hs j x ≠ c x) |>.filter
          (fun j => ¬j ∈ good)).card ≤ k - good.card := by
        apply Finset.card_le_card
        intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
        exact hj.2
      rw [hgood_in] at hpart
      omega
    -- Combine: 2g - k ≤ 2 * wrongGood
    have hthreshold_nat : 2 * good.card - k ≤ 2 * wrongGood := by omega
    -- Cast to ENNReal
    show threshold ≤ G x
    suffices h : (2 * good.card - k : ℕ) ≤ 2 * wrongGood by
      show (↑(2 * good.card - k) : ENNReal) ≤ ∑ j ∈ good, (bad j).indicator (fun _ => (2 : ENNReal)) x
      have hsum_eq : ∑ j ∈ good, (bad j).indicator (fun _ => (2 : ENNReal)) x
          = ↑(2 * wrongGood) := by
        simp only [bad, Set.indicator_apply, Set.mem_setOf_eq]
        trans (∑ j ∈ good, if hs j x ≠ c x then (2 : ENNReal) else 0)
        · rfl
        trans (↑(∑ j ∈ good, if hs j x ≠ c x then 2 else 0 : ℕ))
        · congr 1
          apply Finset.sum_congr rfl
          intro j _
          split <;> simp
        · congr 1
          have : ∑ j ∈ good, (if hs j x ≠ c x then 2 else 0 : ℕ)
              = 2 * (good.filter (fun j => hs j x ≠ c x)).card := by
            simp only [Finset.sum_boole, mul_comm]
          exact this
      rw [hsum_eq]
      exact_mod_cast h
    exact hthreshold_nat
  -- Integral bound: ∫ G dD ≤ ofReal(2 * good.card * ρ)
  have hG_int :
      ∫⁻ x, G x ∂D ≤ ENNReal.ofReal (2 * ↑good.card * ρ) := by
    have hsum_ae :
        ∀ j ∈ good,
          AEMeasurable ((bad j).indicator (fun _ => (2 : ENNReal))) D := by
      intro j _
      exact (Measurable.indicator measurable_const (hbad_meas j)).aemeasurable
    calc
      ∫⁻ x, G x ∂D
          = ∑ j ∈ good, ∫⁻ x, (bad j).indicator (fun _ => (2 : ENNReal)) x ∂D := by
              exact lintegral_finset_sum' good hsum_ae
      _ ≤ ∑ j ∈ good, ENNReal.ofReal (2 * ρ) := by
            apply Finset.sum_le_sum
            intro j hj
            rw [lintegral_indicator_const (hbad_meas j)]
            calc (2 : ENNReal) * D (bad j)
                ≤ 2 * ENNReal.ofReal ρ := mul_le_mul_left' (hgooderr j hj) _
              _ = ENNReal.ofReal (2 * ρ) := by
                    rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
      _ = ↑good.card * ENNReal.ofReal (2 * ρ) := by
            rw [Finset.sum_const, nsmul_eq_mul]
      _ = ENNReal.ofReal (2 * ↑good.card * ρ) := by
            rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
            ring_nf
  -- Markov's inequality
  have hthresh_ne_zero : threshold ≠ 0 := by
    show (↑(2 * good.card - k) : ENNReal) ≠ 0
    exact_mod_cast hden_pos_nat.ne'
  have hthresh_ne_top : threshold ≠ ⊤ := ENNReal.natCast_ne_top _
  have hmarkov :
      D {x : X | threshold ≤ G x}
        ≤ (∫⁻ x, G x ∂D) / threshold :=
    meas_ge_le_lintegral_div hG_ae hthresh_ne_zero hthresh_ne_top
  -- Ratio bound: integral / threshold ≤ ofReal(7 * ρ)
  have hratio :
      (∫⁻ x, G x ∂D) / threshold ≤ ENNReal.ofReal (7 * ρ) := by
    rw [ENNReal.div_le_iff (Or.inl hthresh_ne_zero) (Or.inl hthresh_ne_top)]
    calc ∫⁻ x, G x ∂D
          ≤ ENNReal.ofReal (2 * ↑good.card * ρ) := hG_int
      _ ≤ ENNReal.ofReal (7 * ρ) * threshold := by
            show ENNReal.ofReal (2 * ↑good.card * ρ)
              ≤ ENNReal.ofReal (7 * ρ) * (↑(2 * good.card - k) : ENNReal)
            rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
            apply ENNReal.ofReal_le_ofReal
            have hgf : (7 : ℝ) * ↑k ≤ 12 * ↑good.card := by exact_mod_cast hgoodfrac
            have hcast : (↑(2 * good.card - k) : ℝ) = 2 * ↑good.card - ↑k := by
              rw [Nat.cast_sub (by omega : k ≤ 2 * good.card)]
              push_cast; ring
            rw [hcast]
            nlinarith
  -- Chain the bounds
  calc
    D {x : X | boosted_majority k (fun j => hs j x) ≠ c x}
        ≤ D {x : X | threshold ≤ G x} := D.mono hmajority_sub
    _ ≤ (∫⁻ x, G x ∂D) / threshold := hmarkov
    _ ≤ ENNReal.ofReal (7 * ρ) := hratio
```

### Key API names (verified compiled)

| API | Used for |
|-----|----------|
| `measurableSet_eq_fun` + `.compl` | `hbad_meas` |
| `Finset.sum_boole` | Count conversion inside `hsum_eq` |
| `Finset.filter_card_add_filter_neg_card_eq_card` | Partition counting (`hwrong_all`, `hwrong_split`) |
| `lintegral_finset_sum'` | Linearity of integral |
| `lintegral_indicator_const` | `∫ 2·𝟙_bad = 2 * D(bad)` |
| `meas_ge_le_lintegral_div` | Markov inequality |
| `ENNReal.div_le_iff (Or.inl ...) (Or.inl ...)` | Ratio bound |
| `ENNReal.ofReal_ofNat` | `(2 : ENNReal) = ofReal 2` |
| `ENNReal.ofReal_natCast` | `↑n = ofReal ↑n` |
| `Nat.cast_sub (by omega)` | `↑(2g - k) = 2↑g - ↑k` |
| `nlinarith` | Final `2g*ρ ≤ 7ρ*(2g-k)` |

### Negative space (from JSONL: 3 iterations needed)

**Iteration 1 failed on `hbad_meas`**: Tried `(hhs_meas j).isOpen_preimage _ trivial` — wrong API. Fix: `measurableSet_eq_fun` + `.compl`.

**Iteration 2 failed on `hratio`**: Had `sorry` inside the ratio bound. Missing `Nat.cast_sub`. Fix: explicit `Nat.cast_sub (by omega : k ≤ 2 * good.card)` + `push_cast; ring`.

**Iteration 3 compiled.** The proof above is from iteration 3.

### Estimated LOC: ~130

### Guardrails
- A4/A5 checks
- No new sorry
- Edit only line 706 (will expand to ~130 lines)
- Do not touch any other lemma
- NEVER run `git checkout`, `git restore`, or any working-tree discard command