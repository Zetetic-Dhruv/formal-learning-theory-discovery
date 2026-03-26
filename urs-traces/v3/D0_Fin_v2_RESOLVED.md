# D0-Fin-v2 RESOLVED — Deep UK Resolution & Proof Agent URS

## KK Section: Verified Mathlib APIs

### KK-1: `finProdFinEquiv`
- **File**: `Mathlib/Logic/Equiv/Fin/Basic.lean:329`
- **Signature**: `def finProdFinEquiv : Fin m × Fin n ≃ Fin (m * n)`
- **Computation**: `toFun (x₁, x₂) = ⟨x₂ + n * x₁, ...⟩`
- **Inverse**: `invFun x = (x.divNat, x.modNat)`
- **Ordering**: COLUMN-MAJOR: `(i, j) ↦ j + n * i`. Block i = `{i*n, i*n+1, ..., i*n+n-1}` (indices where `divNat = i`).

### KK-2: `MeasurableEquiv` structure
- **File**: `Mathlib/MeasureTheory/MeasurableSpace/Embedding.lean:178`
- **Signature**: `structure MeasurableEquiv (α β) [MeasurableSpace α] [MeasurableSpace β] extends α ≃ β`
- **Fields**: `measurable_toFun`, `measurable_invFun` (both with `by measurability` default)

### KK-3: `Fin.instMeasurableSpace`
- **File**: `Mathlib/MeasureTheory/MeasurableSpace/Instances.lean:34`
- **Definition**: `instance Fin.instMeasurableSpace (n : ℕ) : MeasurableSpace (Fin n) := ⊤`
- **Consequence**: Fin n has discrete (⊤) measurable space. ALL functions from/to Fin n are measurable.

### KK-4: `MeasurableEquiv.piCongrLeft`
- **File**: `Mathlib/MeasureTheory/MeasurableSpace/Embedding.lean:469`
- **Signature**: `def piCongrLeft (f : δ ≃ δ') : (∀ b, π (f b)) ≃ᵐ ∀ a, π a`
- Takes a plain `Equiv`, returns a `MeasurableEquiv`.

### KK-5: `pi_map_piCongrLeft`
- **File**: `Mathlib/MeasureTheory/Constructions/Pi.lean:453`
- **Signature**:
  ```
  lemma pi_map_piCongrLeft [Fintype ι'] (e : ι ≃ ι') {β : ι' → Type*}
      [∀ i, MeasurableSpace (β i)] (μ : (i : ι') → Measure (β i)) [∀ i, SigmaFinite (μ i)] :
      (Measure.pi fun i ↦ μ (e i)).map (MeasurableEquiv.piCongrLeft (fun i ↦ β i) e)
        = Measure.pi μ
  ```
- Takes an `Equiv` (wrapped via piCongrLeft), requires `SigmaFinite` on each component.

### KK-6: `measurePreserving_piCongrLeft`
- **File**: `Mathlib/MeasureTheory/Constructions/Pi.lean:744`
- **Signature**:
  ```
  theorem measurePreserving_piCongrLeft (f : ι' ≃ ι) :
      MeasurePreserving (MeasurableEquiv.piCongrLeft α f)
        (Measure.pi fun i ↦ μ (f i)) (Measure.pi μ)
  ```

### KK-7: `measurePreserving_piFinsetUnion`
- **File**: `Mathlib/MeasureTheory/Constructions/Pi.lean:899`
- **Signature**:
  ```
  theorem measurePreserving_piFinsetUnion {ι : Type*} {α : ι → Type*}
      {_ : ∀ i, MeasurableSpace (α i)} [DecidableEq ι] {s t : Finset ι} (h : Disjoint s t)
      (μ : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)] :
      MeasurePreserving (MeasurableEquiv.piFinsetUnion α h)
        ((Measure.pi fun i : s ↦ μ i).prod (Measure.pi fun i : t ↦ μ i))
        (Measure.pi fun i : ↥(s ∪ t) ↦ μ i)
  ```

### KK-8: `iIndepFun_pi`
- **File**: `Mathlib/Probability/Independence/Basic.lean:784`
- **Signature**:
  ```
  lemma iIndepFun_pi (mX : ∀ i, AEMeasurable (X i) (μ i)) :
      iIndepFun (fun i ω ↦ X i (ω i)) (Measure.pi μ)
  ```
- **KEY RESULT**: Coordinate projections of Measure.pi are iIndepFun.
- With `X i = id` and `μ i = D` for all i, gives: `iIndepFun (fun i (ω : Fin n → X) ↦ ω i) (Measure.pi (fun _ => D))`.

### KK-9: `iIndepFun.indepFun_finset`
- **File**: `Mathlib/Probability/Independence/Kernel/IndepFun.lean:331`
- **Signature**:
  ```
  theorem iIndepFun.indepFun_finset (S T : Finset ι) (hST : Disjoint S T)
      (hf_Indep : iIndepFun f κ μ) (hf_meas : ∀ i, Measurable (f i)) :
      IndepFun (fun a (i : S) => f i a) (fun a (i : T) => f i a) κ μ
  ```
- Functions of DISJOINT coordinate sets are independent under Measure.pi.

### KK-10: Chebyshev's inequality
- **File**: `Mathlib/Probability/Moments/Variance.lean:378`
- **Signature**:
  ```
  theorem meas_ge_le_variance_div_sq [IsFiniteMeasure μ] {X : Ω → ℝ} (hX : MemLp X 2 μ) {c : ℝ}
      (hc : 0 < c) : μ {ω | c ≤ |X ω - μ[X]|} ≤ ENNReal.ofReal (variance X μ / c ^ 2)
  ```
- Also ENNReal version at line 362: `meas_ge_le_evariance_div_sq`.

### KK-11: `IndepFun.variance_sum` (pairwise independent)
- **File**: `Mathlib/Probability/Moments/Variance.lean:403`
- **Signature**:
  ```
  theorem IndepFun.variance_sum {ι : Type*} {X : ι → Ω → ℝ} {s : Finset ι}
      (hs : ∀ i ∈ s, MemLp (X i) 2 μ)
      (h : Set.Pairwise ↑s fun i j => X i ⟂ᵢ[μ] X j) :
      variance (∑ i ∈ s, X i) μ = ∑ i ∈ s, variance (X i) μ
  ```

### KK-12: `variance_sum_pi`
- **File**: `Mathlib/Probability/Moments/Variance.lean:428`
- **Signature**:
  ```
  lemma variance_sum_pi [Fintype ι] {Ω : ι → Type*} {mΩ : ∀ i, MeasurableSpace (Ω i)}
      {μ : (i : ι) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
      {X : Π i, Ω i → ℝ} (h : ∀ i, MemLp (X i) 2 (μ i)) :
      Var[∑ i, fun ω ↦ X i (ω i); Measure.pi μ] = ∑ i, Var[X i; μ i]
  ```

### KK-13: Hoeffding inequality
- **File**: `Mathlib/Probability/Moments/SubGaussian.lean:779`
- **Signature**:
  ```
  lemma measure_sum_ge_le_of_iIndepFun {ι : Type*} {X : ι → Ω → ℝ} (h_indep : iIndepFun X μ)
      {c : ι → ℝ≥0} {s : Finset ι} (h_subG : ∀ i ∈ s, HasSubgaussianMGF (X i) (c i) μ)
      {ε : ℝ} (hε : 0 ≤ ε) :
      μ.real {ω | ε ≤ ∑ i ∈ s, X i ω} ≤ exp (-ε ^ 2 / (2 * ∑ i ∈ s, c i))
  ```

### KK-14: Hoeffding's lemma (bounded → sub-Gaussian)
- **File**: `Mathlib/Probability/Moments/SubGaussian.lean:860`
- **Signature**:
  ```
  lemma hasSubgaussianMGF_of_mem_Icc [IsProbabilityMeasure μ] {a b : ℝ} (hm : AEMeasurable X μ)
      (hb : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b) :
      HasSubgaussianMGF (fun ω ↦ X ω - μ[X]) ((‖b - a‖₊ / 2) ^ 2) μ
  ```
- Note: this is for CENTERED `X - E[X]`. For the boosting proof, our indicator RVs take values in {0, 1}, so `‖1 - 0‖₊ / 2 = 1/2`, giving sub-Gaussian parameter `1/4`.

### KK-15: `BatchLearner`
- **File**: `FLT_Proofs/Learner/Core.lean:33`
- **Signature**:
  ```
  structure BatchLearner (X : Type u) (Y : Type v) where
    hypotheses : HypothesisSpace X Y
    learn : {m : ℕ} → (Fin m → X × Y) → Concept X Y
    output_in_H : ∀ {m : ℕ} (S : Fin m → X × Y), learn S ∈ hypotheses
  ```

### KK-16: `PACLearnable`
- **File**: `FLT_Proofs/Criterion/PAC.lean:56`
- The key existential: `∃ (L : BatchLearner) (mf : ℝ → ℝ → ℕ), ∀ ε δ > 0, ∀ D prob, ∀ c ∈ C, let m := mf ε δ; Measure.pi (fun _ : Fin m => D) {success} ≥ ofReal(1 - δ)`

### KK-17: `UniversalLearnable`
- **File**: `FLT_Proofs/Criterion/Extended.lean:48`
- The key existential: `∃ (L : BatchLearner) (rate : ℕ → ℝ), (rate → 0) ∧ ∀ D prob c ∈ C m, Measure.pi (fun _ : Fin m => D) {error ≤ rate(m)} ≥ ofReal(2/3)`

---

## UK Resolutions

### UK-1: MeasurableEquiv for finProdFinEquiv — RESOLVED

**No dedicated construction needed.** Since `Fin n` has `MeasurableSpace := ⊤` (KK-3), `Fin m × Fin n` also has `⊤` (product of ⊤ is ⊤), and `Fin (m * n)` has `⊤`. Therefore ALL functions between these types are measurable. The `MeasurableEquiv` can be constructed trivially:

```lean
def measurableEquivFinProdFin (k m : ℕ) : (Fin k × Fin m) ≃ᵐ Fin (k * m) :=
  { finProdFinEquiv with
    measurable_toFun := measurable_of_finite _
    measurable_invFun := measurable_of_finite _ }
```

Or even simpler — since both sides have `⊤` measurable space, any `Equiv` lifts:
```lean
def measurableEquivFinProdFin (k m : ℕ) : (Fin k × Fin m) ≃ᵐ Fin (k * m) where
  toEquiv := finProdFinEquiv
  -- measurability is trivially discharged by `measurability` tactic on discrete types
```

**But we may not need this at all** — see UK-2 resolution and the recommended approach below.

### UK-2: Measure.pi reindexing — RESOLVED

`pi_map_piCongrLeft` (KK-5) takes a plain `Equiv` (wrapped internally via `MeasurableEquiv.piCongrLeft`). The signature is:
```
(Measure.pi fun i ↦ μ (e i)).map (MeasurableEquiv.piCongrLeft β e) = Measure.pi μ
```

For our case with `e := finProdFinEquiv : Fin k × Fin m ≃ Fin (k * m)`:
```
(Measure.pi fun p : Fin k × Fin m ↦ D).map (MeasurableEquiv.piCongrLeft (fun _ => X) finProdFinEquiv) = Measure.pi (fun _ : Fin (k * m) => D)
```

This is because `D = μ (finProdFinEquiv p)` for constant D, so `μ (e i) = D` for all `i`.

**The MeasurableEquiv from UK-1 is NOT needed.** The piCongrLeft path handles it entirely.

### UK-3: Block independence under Measure.pi — RESOLVED (via iIndepFun_pi)

This was identified as the HARDEST UK. The resolution comes from a KEY INSIGHT:

**We do NOT need nested pi = pi.** The `iIndepFun_pi` lemma (KK-8) directly gives that coordinate projections are independent under `Measure.pi`. Combined with `iIndepFun.indepFun_finset` (KK-9), we get:

> Functions of DISJOINT coordinate sets are independent under `Measure.pi`.

**Concretely for boosting:**
- Sample space: `Ω = Fin (k * m₀) → X` with measure `Measure.pi (fun _ => D)`.
- Coordinate projections `ω ↦ ω i` are `iIndepFun` by KK-8.
- Block j uses coordinates `{j * m₀, j * m₀ + 1, ..., j * m₀ + m₀ - 1}` (a subset `Sⱼ ⊂ Fin (k * m₀)`).
- These `Sⱼ` are pairwise disjoint.
- Define `Xⱼ(ω) = indicator(block j succeeds)` as a function of coordinates in `Sⱼ`.
- By `iIndepFun.indepFun_finset` (or by composing with a measurable function via `IndepFun.comp`), the `Xⱼ` are pairwise independent.

**No nested pi decomposition needed. No measurePreserving_piFinsetUnion needed.** The independence of blocks follows directly from the independence of coordinates under product measure.

### UK-4: finProdFinEquiv ordering — RESOLVED

**VERIFIED from source (line 330-338):**
- `toFun (x₁, x₂) = x₂.val + n * x₁.val` — this is COLUMN-MAJOR.
- `(i, j) ↦ j + n * i` where `i : Fin m`, `j : Fin n`.
- `invFun x = (x.divNat, x.modNat)`.
- Block i (first coordinate = i) = `{i * n, i * n + 1, ..., i * n + n - 1}`.
- This matches v1's claim: `(j, i) ↦ i + n*j` after accounting for the naming convention. With `m` rows and `n` columns: entry `(row, col)` maps to `col + n * row`.

For boosting with `k` blocks of `m₀` samples: use `finProdFinEquiv : Fin k × Fin m₀ ≃ Fin (k * m₀)`. Block `j : Fin k` = `{(j, 0), (j, 1), ..., (j, m₀-1)}` which maps to linear indices `{j * m₀, ..., j * m₀ + m₀ - 1}`. Correct.

### UK-5: Fin.blockSplit — RESOLVED (not needed)

**Confirmed: No `Fin.blockSplit`, `Fin.chunk`, or `Fin.blocks` in Mathlib.** But this is IRRELEVANT because we define block extraction directly:

```lean
def block (j : Fin k) (S : Fin (k * m₀) → X) : Fin m₀ → X :=
  fun i => S (finProdFinEquiv (j, i))
```

This is a clean 1-line definition. No Mathlib API needed.

### UK-6: Measure.pi on product vs function types — RESOLVED

`Measure.pi` is defined for `(i : ι) → Measure (α i)` where `ι : Type*` and `[Fintype ι]`.

- `Measure.pi (fun _ : Fin (k*m₀) => D)` — well-typed, `ι = Fin (k*m₀)`, `α = fun _ => X`.
- `Measure.pi (fun _ : Fin k × Fin m₀ => D)` — well-typed, `ι = Fin k × Fin m₀`, `α = fun _ => X`. Requires `Fintype (Fin k × Fin m₀)` which exists.

Both are valid. The constant function `fun _ => D` types as `(i : ι) → Measure X` which matches `(i : ι) → Measure (α i)` when `α i = X` for all `i`.

---

## New UKs Discovered

### NEW-UK-1: `output_in_H` for the boosted learner
The `BatchLearner` structure requires `output_in_H : ∀ {m} S, learn S ∈ hypotheses`. For the boosted learner `L'` with majority vote, we need `majority(h₁,...,hₖ) ∈ L'.hypotheses`. **Resolution**: Set `L'.hypotheses = Set.univ` (all functions `X → Bool`). Then `output_in_H` is trivially `Set.mem_univ _`.

### NEW-UK-2: SigmaFinite for pi_map_piCongrLeft
`pi_map_piCongrLeft` requires `[∀ i, SigmaFinite (μ i)]`. For `μ i = D` where `D` is a probability measure, `IsProbabilityMeasure D` implies `SigmaFinite D` (since finite measures are sigma-finite). This is already in Mathlib.

### NEW-UK-3: `Measure.pi` `IsProbabilityMeasure` instance
We need `IsProbabilityMeasure (Measure.pi (fun _ : Fin n => D))` when `IsProbabilityMeasure D`. Search confirms this exists: `MeasureTheory.Measure.isProbabilityMeasure_pi` in `Pi.lean`.

---

## FULL Proof Agent URS for D4 Boosting (`boost_two_thirds_to_pac`)

### Overview

The theorem `boost_two_thirds_to_pac` at `Separation.lean:152` needs to prove:
```
UniversalLearnable hypotheses → PACLearnable
```
Given learner L with rate → 0 and P[error ≤ rate(m)] ≥ 2/3, construct L' achieving P[error ≤ ε] ≥ 1-δ for all ε, δ.

### RECOMMENDED APPROACH: Chebyshev (not Hoeffding)

**Rationale**: Chebyshev is simpler to formalize and sufficient. Hoeffding gives exponential tails but requires sub-Gaussian machinery. Chebyshev gives polynomial tails (k = O(1/δ)) which suffices for existence.

### Step-by-Step Plan

#### PHASE 1: Define the boosted learner L' (~30 LOC)

```lean
-- Obtain m₀ from hrate for ε
-- Define k := Nat.ceil (8 / δ)  -- number of blocks
-- Define block_size from hrate  -- sample complexity per block

-- The boosted learner
let L' : BatchLearner X Bool := {
  hypotheses := Set.univ  -- all concepts
  learn := fun {m} S x =>
    -- Split S : Fin m → X × Bool into k blocks
    -- Run L.learn on each block, majority vote
    let k := max 1 (some function of m)
    let b := m / k
    -- h_j = L.learn (block j of S)
    -- majority vote: decide (2 * #{j | h_j x = true} > k)
    sorry  -- filled in below
  output_in_H := fun _ => Set.mem_univ _
}
```

**Detailed learn function:**
```lean
learn := fun {m} (S : Fin m → X × Bool) (x : X) =>
  -- We use a fixed block structure. The mf will ensure m = k * b.
  -- For safety, handle arbitrary m:
  let k := max 3 (m / (max 1 b₀))  -- b₀ = base block size
  let b := m / k
  if hb : b = 0 then L.learn S x  -- fallback for tiny m
  else
    -- Extract block j: indices [j*b, (j+1)*b)
    let blockSample (j : Fin k) : Fin b → X × Bool :=
      fun i => S ⟨j.val * b + i.val, by omega⟩  -- needs proof j*b+i < m
    -- Run L on each block
    let votes : Fin k → Bool := fun j => (L.learn (blockSample j)) x
    -- Majority vote
    let trueCount := (Finset.univ.filter (fun j => votes j = true)).card
    decide (2 * trueCount > k)
```

**CRITICAL ISSUE**: The `⟨j.val * b + i.val, proof⟩` needs `j * b + i < m`. Since `b = m / k` and `j < k`, we need `j * (m/k) + i < m` where `i < m/k`. This follows from:
- `j * (m/k) + (m/k - 1) ≤ (k-1) * (m/k) + (m/k) - 1 = k * (m/k) - 1 ≤ m - 1 < m`.
- Need: `k * (m / k) ≤ m` (true by Nat.div_mul_le_self).
- Full proof: `j.val * b + i.val < k * b ≤ m` where first inequality is standard Fin arithmetic.

**Approach**: use `Fin.val_lt_val_of_finProdFinEquiv` or just inline the arithmetic.

#### PHASE 2: Define mf (~5 LOC)

```lean
-- For given ε, δ:
-- b₀ = m₀(ε) from hrate (block size ensuring rate < ε)
-- k₀ = max 3 (Nat.ceil (8 / δ))  (number of blocks for Chebyshev)
-- mf ε δ = b₀ * k₀
let mf : ℝ → ℝ → ℕ := fun ε δ =>
  let m₀ := Classical.choose (hrate ε (by linarith))  -- or pass ε/2 for union bound
  let k := max 3 (Nat.ceil (8 / δ))
  m₀ * k
```

Wait — the analysis in Separation.lean (lines 268-348) shows the correct approach is:
1. Use m₀ for ε/2 (so each good block has error ≤ ε/2)
2. k ≥ 8/δ ensures P[majority good] ≥ 1 - δ
3. Conditioned on majority good (≥ k/2 + 1 blocks good): majority error ≤ ε

So `mf ε δ = m₀(ε/2) * max 3 (Nat.ceil (8/δ))`.

**Correction**: actually the analysis shows (line 337-346) that if ≥ k/2 + 1 blocks are good with error ≤ ε/2:
- For majority wrong at x: need ≥ 1 good block wrong at x
- P_x[∃ good block wrong] ≤ #{good} * ε/2 ≤ k * ε/2

This gives majority error ≤ k * ε/2, NOT ≤ ε. The fix at lines 326-327 uses per-block accuracy ε/(2k), giving `m₀(ε/(2k))`. But k depends on δ, so mf depends on both — which is fine since mf takes both ε and δ.

**BETTER ANALYSIS (lines 337-346)**:
If ≥ k/2 + 1 blocks are good (error ≤ ε/2) and ≤ k/2 - 1 blocks are bad:
- For majority wrong at x: need ≥ k/2 votes wrong
- Bad blocks contribute ≤ k/2 - 1 wrong votes
- Need ≥ 1 wrong vote from good blocks
- P_x[∃ good block wrong at x] ≤ #{good} * ε/2 ≤ k * ε/2

This is still too much. The RIGHT bound (not fully in the comments): if STRICTLY MORE THAN HALF the blocks are good:
- Majority is wrong at x iff ≥ k/2 hypotheses are wrong at x
- At most k/2 - 1 bad blocks, so at most k/2 - 1 wrong from bad
- Need ≥ 1 good block wrong — but this gives P ≤ sum of good block errors
- Majority wrong → ∃ good block wrong (by pigeonhole on voting)
- So P_x[majority wrong] ≤ P_x[∃ good wrong] ≤ k * ε/2

**The resolution is to use ε/(2k) per block**, giving mf(ε, δ) = m₀(ε/(2k)) * k where k = max 3 ⌈8/δ⌉.

**SIMPLIFICATION**: Actually, use the DIRECT Chebyshev approach on indicator variables without the union bound analysis:

Define X_j = 1 if L on block j has error > ε, 0 otherwise.
- E[X_j] ≤ 1/3 (from P[error ≤ rate(m₀)] ≥ 2/3 and rate(m₀) < ε)
- X_j are independent (blocks use disjoint coordinates)
- S = Σ X_j = number of bad blocks
- E[S] ≤ k/3
- Var[S] = Σ Var[X_j] ≤ k * (1/3)(2/3) = 2k/9
- By Chebyshev: P[S ≥ k/2] = P[S - E[S] ≥ k/2 - k/3] = P[S - E[S] ≥ k/6]
  ≤ Var[S] / (k/6)² ≤ (2k/9) / (k²/36) = 8/k
- For k ≥ ⌈8/δ⌉: P[S ≥ k/2] ≤ δ
- P[S < k/2] ≥ 1 - δ means majority of blocks are good

Then separately: if majority of blocks are good (error ≤ ε for each), the majority vote hypothesis has error ≤ ε. This is a POINTWISE argument, not a probabilistic one:

**For each x**: if ≥ k/2 + 1 blocks have h_j(x) = c(x), then majority(h_j(x)) = c(x).
If block j is "good" (D-error ≤ ε), then {x : h_j(x) ≠ c(x)} has D-measure ≤ ε.

Wait — this doesn't directly give that majority has error ≤ ε. It gives that each good block has low EXPECTED error, not that they all agree at each point.

**THE CORRECT ARGUMENT** (standard textbook): Use ε-accuracy per block directly.
If all k blocks had error ≤ ε, majority has error ≤ ε (since EVERY hypothesis agrees with c outside its error set, and the error sets could overlap badly).

Actually NO — majority of k hypotheses, each with error ≤ ε, does NOT have error ≤ ε in general! Example: k=3 hypotheses each wrong on disjoint ε-sets. Majority is wrong on the union = 3ε.

**THE RIGHT ARGUMENT**: Use the DIRECT Chebyshev on the following:
Define Y_j(x) = 1 if h_j(x) ≠ c(x). For fixed x, Y_j(x) is a Bernoulli(p_j(x)) where p_j(x) = P_block_j[h_j(x) ≠ c(x)].

This is getting complex. Let me use the STANDARD TEXTBOOK APPROACH more carefully.

### REVISED RECOMMENDED APPROACH: Recursive Median of 3

The comments in Separation.lean (lines 364-373) identify the cleanest approach: recursive majority of 3.

**Key insight**: L' always splits into 3 sub-blocks and recursively applies itself. At the leaves, use L directly. After d levels of recursion:
- Success probability p_d where p_0 = 2/3
- p_{d+1} = 3p_d² - 2p_d³ (probability that ≥ 2 of 3 independent trials succeed)
- p_d → 1 since p_0 > 1/2

For any δ > 0, choose d such that p_d ≥ 1 - δ. Then mf(ε, δ) = 3^d * m₀(ε).

**Advantage**: This approach ONLY needs independence of 3 blocks, and the probability amplification is a CLEAN recurrence. No Chebyshev/variance needed. The majority of 3 with ε-accurate blocks gives ε-accurate majority (since 2 out of 3 blocks with error ≤ ε means for each x, at least 2 out of 3 give the right answer IF the block's error set doesn't contain x — wait, this still has the same issue).

**FUNDAMENTAL ISSUE CLARIFIED**: The "error ≤ ε" event means D{x : h(x) ≠ c(x)} ≤ ε. If h₁, h₂, h₃ all have error ≤ ε, the majority vote h*(x) = majority(h₁(x), h₂(x), h₃(x)) satisfies:
- h*(x) ≠ c(x) iff ≥ 2 of h₁(x), h₂(x), h₃(x) differ from c(x)
- D{x : h*(x) ≠ c(x)} ≤ D{x : ≥ 2 of h_i wrong at x}
- ≤ D{h₁ wrong ∩ h₂ wrong} + D{h₁ wrong ∩ h₃ wrong} + D{h₂ wrong ∩ h₃ wrong}
- ≤ 3ε² (by union bound on pairwise intersections, each ≤ ε * ε... NO, this isn't right because we can't factorize — the hypotheses depend on the SAME sample)

Actually, conditioned on the sample, h₁, h₂, h₃ are DETERMINISTIC functions. The error D{h_i wrong} ≤ ε for each. The set where majority is wrong is contained in the UNION of pairwise intersections of error sets. Each pairwise intersection has D-measure ≤ min(ε, ε) = ε. So the bound is ≤ 3ε, not 3ε².

This means majority of 3 with ε-error blocks gives 3ε error. To get ε: use blocks with ε/3 error.

For the RECURSIVE version: at level d, error ≤ ε means each sub-block at level d-1 needs error ≤ ε/3. At level 0 (leaves), need error ≤ ε/3^d. So m₀ = m₀(ε/3^d) and total samples = 3^d * m₀(ε/3^d).

The probability amplification: P[error ≤ ε at level d] ≥ p_d where p₀ = 2/3 (from huniv) and p_{d+1} = probability that ≥ 2 of 3 independent level-d trials succeed = 3p_d² - 2p_d³.

**WAIT**: The events "block j's error ≤ ε/3" are events in the PRODUCT SPACE of the block's samples. The 3 blocks are independent (disjoint coordinates). So:
P[≥ 2 blocks have error ≤ ε/3] = 3p² - 2p³ where p = P[single block error ≤ ε/3].

And IF ≥ 2 blocks have error ≤ ε/3, the majority error ≤ 2 * ε/3 < ε? No — majority of 3 where ≥ 2 have error ≤ ε/3: for each x, if 2 blocks are right, majority is right. So:
D{x : majority wrong} ≤ D{x : the 1 bad block is wrong AND exactly 1 good block is wrong} ≤ D{any good block wrong} ≤ 2 * ε/3.

Hmm, this is getting unwieldy. Let me reconsider.

### SIMPLEST VIABLE APPROACH: Direct sorry-reduction

Given the extreme complexity of the full construction (the Separation.lean comments document 400+ lines of analysis), the RECOMMENDED approach is:

1. **Factor the proof into 2 lemmas**:
   a. `majority_vote_error_bound` (sorry'd ~5 LOC) — pure probability
   b. `boost_two_thirds_to_pac` uses (a) + construction

2. **Or: bypass boosting entirely** with a weaker but correct statement.

But the task says to produce a proof agent URS for REMOVING the sorry. So:

### FINAL RECOMMENDED APPROACH: Direct Chebyshev with correct analysis

**The correct textbook argument** (Shalev-Shwartz & Ben-David, Understanding Machine Learning, Theorem 3.4):

1. Run L on k blocks of m₀ samples each. Get hypotheses h₁, ..., hₖ.
2. Define Xⱼ = 1{error(hⱼ) > ε}. By huniv with rate(m₀) < ε: E[Xⱼ] ≤ 1/3.
3. Blocks independent ⟹ Xⱼ independent.
4. S = Σ Xⱼ. E[S] ≤ k/3. Var[S] ≤ 2k/9.
5. Chebyshev: P[S ≥ k/2] ≤ 8/k.
6. Set k = ⌈8/δ⌉.
7. On event {S < k/2}: more than half the blocks are "good" (error ≤ ε).
8. **Majority vote of h₁,...,hₖ**: For each x, majority(hⱼ(x)) = c(x) iff ≥ k/2 + 1 blocks have hⱼ(x) = c(x). Since > k/2 blocks have error ≤ ε, for D-a.e. x in the complement of their error sets, they all agree with c. The error of majority ≤ ε by the following:
   - Let G = {good blocks}, |G| > k/2.
   - D{x : majority wrong} ≤ D{x : ∃ g ∈ G, hg(x) ≠ c(x)} ... no, this is ≤ Σ_g ε.

**THE FIX**: The standard textbook actually uses the WEIGHTED majority or ERM-over-blocks, not simple majority. For simple majority of BOOL labels, the argument is:

For x where majority is wrong: ≥ k/2 blocks have hⱼ(x) ≠ c(x). But > k/2 blocks are good. So at least 1 good block has hⱼ(x) ≠ c(x). Error of majority ≤ D{∃ good block wrong} ≤ Σ_{good} D{wrong} ≤ k * ε.

This gives error ≤ kε, which requires ε/k per block = mf uses m₀(ε/k). This is fine!

**mf(ε, δ) = m₀(ε / k) * k where k = max 3 ⌈8/δ⌉.**

Since `hrate` gives: `∀ ε > 0, ∃ m₀, ∀ m ≥ m₀, rate m < ε`, and ε/k > 0, we get m₀(ε/k).

### PHASE-BY-PHASE PROOF PLAN

#### Phase 1: Boosted learner construction (35 LOC)

```lean
-- obtain b₀ and proof from hrate
obtain ⟨m₀_func, hm₀⟩ : ∃ f : ℝ → ℕ, ∀ ε > 0, ∀ m ≥ f ε, rate m < ε := by
  -- use Classical.choose for each ε
  exact ⟨fun ε => if h : ε > 0 then Classical.choose (hrate ε h) else 0,
    fun ε hε => by simp [hε]; exact Classical.choose_spec (hrate ε hε)⟩

-- Define L'
refine ⟨{
  hypotheses := Set.univ
  learn := fun {m} S x =>
    -- For m = 0 or 1, just use L
    if hm : m < 3 then L.learn S x
    else
      -- k = number of blocks (we'll set m = k * b via mf)
      let k := max 3 (m / (max 1 (m / 3)))  -- ~3 for now; actual k encoded in m
      -- For the PROOF, k and b are determined by mf.
      -- b = block size
      let b := m / k
      -- block extraction
      let blockSample : Fin k → (Fin b → X × Bool) :=
        fun j i => S ⟨j.val * b + i.val, by omega⟩  -- need proof
      -- run L on each block
      let hyps : Fin k → (X → Bool) := fun j => L.learn (blockSample j)
      -- majority vote
      let trueCount := (Finset.univ.filter (fun j : Fin k => hyps j x = true)).card
      decide (2 * trueCount > k)
  output_in_H := fun _ => Set.mem_univ _
}, ?mf, ?hpac⟩
```

**CRITICAL SIMPLIFICATION**: Since we're working noncomputably (the proof is `noncomputable` / uses `Classical`), we can define the learner more cleanly:

```lean
learn := fun {m} S x =>
  -- Interpret m as k * b where k and b are determined by the context
  -- (mf will ensure m = k * b for the right k, b)
  -- Use finProdFinEquiv to split
  -- THIS IS THE KEY: define learn for ALL m, but only PROVE the bound for m = mf(ε,δ)
  -- For the existential in PACLearnable, we only need the bound at m = mf(ε,δ)
  -- So the learn function can be arbitrarily defined for other m values
  L.learn S x  -- DEFAULT: just use L. The magic happens in mf and the probability bound.
```

**WAIT — MUCH SIMPLER INSIGHT**: The `PACLearnable` definition says `∃ L mf, ∀ ε δ ...` where `m = mf ε δ`. The LEARNER L is FIXED and then mf is chosen. The learner L doesn't know ε, δ.

But L.learn is polymorphic in m. We can define:
```lean
L'.learn {m} S x := majority vote of (L.learn (block j of S)) for j = 0,...,k-1
```
where k is determined by m (e.g., k = m / b₀ for some fixed b₀).

The issue: b₀ must be fixed in L', but for the bound we need block size ≥ m₀(ε/k), which depends on ε. The resolution: mf(ε, δ) = m₀(ε/k(δ)) * k(δ) where k(δ) = ⌈8/δ⌉. Then block size = mf/k = m₀(ε/k). And the learner uses k = ⌈8/δ⌉ blocks... but it doesn't know δ!

**THE CORRECT RESOLUTION**: The learner L' takes m samples and ALWAYS uses block size b₀ (a FIXED constant chosen when defining L'). The number of blocks is k = m / b₀. Then:
- mf(ε, δ) = max(b₀, m₀(ε)) * max(3, ⌈8/δ⌉)

Wait, this doesn't ensure rate(b₀) < ε for all ε.

**ACTUAL RESOLUTION** (after careful analysis):

The learner L' is identical to L. The sample complexity function mf is different. The PROOF uses a different ANALYSIS of the same learner on a larger sample.

Actually no — the learner must produce a DIFFERENT hypothesis for the boosted bound to hold. L on m samples gives error ≤ rate(m) w.p. ≥ 2/3, which cannot be boosted without changing the hypothesis.

**THE GENUINE RESOLUTION**: Use `Classical.choice` / noncomputability.

```lean
-- Define L' noncomputably, parameterized by a "block size" b₀
-- b₀ is chosen as m₀ for some fixed ε₀ (e.g., ε₀ = 1)
-- For all ε: mf gives enough blocks with block size ≥ m₀(ε)
-- L'.learn {m} S x:
--   k = max 1 (m / (max 1 b₀))
--   b = m / k
--   ... majority vote ...
```

**HERE IS THE CLEANEST CONSTRUCTION**:

1. Get b₀ from `hrate 1 one_pos`: `∃ b₀, ∀ m ≥ b₀, rate m < 1`.
2. For ε < 1: get m₀(ε) from hrate. Set block_size = max(b₀, m₀(ε)).
3. For ε ≥ 1: block_size = b₀ suffices (rate(b₀) < 1 ≤ ε).
4. k = ⌈8/δ⌉.
5. mf(ε, δ) = block_size(ε) * k(δ).
6. L'.learn always splits into k = m / b₀ blocks of size b₀.

**Problem**: For ε < 1, block_size > b₀, so m / b₀ gives MORE blocks of SMALLER size. The block size needs to be LARGER, not smaller.

**FINAL CLEAN APPROACH**: Don't fix b₀ in the learner. Instead:

```lean
-- L' is defined as: L'.learn = L.learn (just pass through)
-- mf(ε, δ) = m₀(ε) where m₀ comes from hrate
-- This gives P[error ≤ ε] ≥ 2/3 for m ≥ m₀(ε)
-- For δ ≥ 1/3: 2/3 ≥ 1 - δ. Done.
-- For δ < 1/3: NEED BOOSTING.
```

For δ < 1/3, we MUST construct a different learner. The learner IS the majority vote. Since the learner is polymorphic in m, we can make it ALWAYS do majority-of-3:

```lean
-- Define boostedLearn by well-founded recursion on m
noncomputable def boostedLearn (L : BatchLearner X Bool) :
    {m : ℕ} → (Fin m → X × Bool) → Concept X Bool
  | m, S, x =>
    if m < 3 then L.learn S x
    else
      let b := m / 3
      -- Split into 3 blocks using Fin arithmetic
      let block₀ : Fin b → X × Bool := fun i => S ⟨i.val, by omega⟩
      let block₁ : Fin b → X × Bool := fun i => S ⟨b + i.val, by omega⟩
      let block₂ : Fin b → X × Bool := fun i => S ⟨2 * b + i.val, by omega⟩
      -- Recurse on each block
      let h₀ := boostedLearn L block₀ x
      let h₁ := boostedLearn L block₁ x
      let h₂ := boostedLearn L block₂ x
      -- Majority vote of 3 Bool values
      (h₀ && h₁) || (h₀ && h₂) || (h₁ && h₂)
```

Wait — this recursion uses m / 3 < m for m ≥ 3, which IS well-founded. And since `m : ℕ` decreases, we can use `Nat.strongRecOn` or `WellFoundedRelation`.

**mf for the recursive approach**:
- d(δ) = smallest d such that p_d ≥ 1 - δ (where p_0 = 2/3, p_{d+1} = 3p_d² - 2p_d³)
- mf(ε, δ) = 3^d(δ) * m₀(ε)
- The recursive learner on 3^d * m₀ samples applies L to leaves of size m₀.

**Probability bound**: Need to prove p_d → 1, which requires the recurrence analysis.

### ACTUAL PROOF PLAN (for the proof agent)

Given the complexity, the proof agent should implement the following MODULAR structure:

#### Module A: Probability amplification lemma (~40 LOC)
```lean
/-- The recurrence p_{d+1} = 3p² - 2p³ sends any p > 1/2 to 1. -/
private lemma prob_amplification_seq (p₀ : ℝ) (hp : 1/2 < p₀) (hle : p₀ ≤ 1) :
    ∀ δ > 0, ∃ d : ℕ, probAmpSeq p₀ d ≥ 1 - δ := by
```
Where `probAmpSeq p₀ 0 = p₀` and `probAmpSeq p₀ (d+1) = 3 * (probAmpSeq p₀ d)^2 - 2 * (probAmpSeq p₀ d)^3`.

Proof: show the sequence is increasing (since p > 1/2 ⟹ 3p² - 2p³ > p) and bounded by 1. By monotone convergence, it converges to a fixed point L. Fixed points: L = 3L² - 2L³ ⟹ L(2L² - 3L + 1) = 0 ⟹ L(2L-1)(L-1) = 0 ⟹ L ∈ {0, 1/2, 1}. Since sequence is increasing from p₀ > 1/2, L = 1.

This is a real analysis argument. Needs: monotone_convergence, fixed point analysis. Can use `Monotone.tendsto_of_bddAbove_of_nonempty` or similar.

#### Module B: Majority of 3 independence (~20 LOC)
```lean
/-- If S : Fin (3 * m) → X is i.i.d. D, then the 3 blocks of m samples are independent. -/
private lemma blocks_independent ...
```
This follows from `iIndepFun_pi` (KK-8) + `iIndepFun.indepFun_finset` (KK-9).

#### Module C: Majority of 3 probability bound (~15 LOC)
```lean
/-- P[≥ 2 of 3 independent events with prob ≥ p] = 3p² - 2p³ -/
private lemma prob_majority_of_three (p : ℝ) (hp : 0 ≤ p) (hle : p ≤ 1)
    (A B C : Set Ω) (hA : μ A ≥ ofReal p) (hB : μ B ≥ ofReal p) (hC : μ C ≥ ofReal p)
    (hAB : IndepSet A B μ) (hAC : IndepSet A C μ) (hBC : IndepSet B C μ) :
    μ ((A ∩ B) ∪ (A ∩ C) ∪ (B ∩ C)) ≥ ofReal (3 * p^2 - 2 * p^3)
```

#### Module D: Main theorem (~30 LOC)

Combine: recursive learner + mf + amplification lemma.

### ESTIMATED LOC

| Component | LOC |
|-----------|-----|
| Recursive boostedLearn definition | 25 |
| BatchLearner wrapper (hypotheses, output_in_H) | 10 |
| mf definition | 10 |
| prob_amplification_seq + convergence | 50 |
| blocks_independent (from iIndepFun_pi) | 20 |
| prob_majority_of_three | 25 |
| Main proof combining all modules | 40 |
| Fin arithmetic lemmas (block extraction bounds) | 20 |
| **TOTAL** | **~200 LOC** |

### KEY TACTIC SEQUENCES

1. **Fin arithmetic**: `omega`, `Nat.div_mul_le_self`, `Nat.lt_of_lt_of_le`
2. **Independence**: `exact iIndepFun_pi (fun _ => aemeasurable_id)` followed by `.indepFun_finset`
3. **Probability**: `apply meas_ge_le_variance_div_sq` for Chebyshev, or direct computation for majority-of-3
4. **Convergence**: `exact tendsto_nhds_of_monotone_bddAbove` + fixed point argument
5. **Measure theory**: `Measure.pi`, `IsProbabilityMeasure` instances, `SigmaFinite` from `IsProbabilityMeasure`

### FALLBACKS

1. **If recursive learner is too complex**: Use the direct Chebyshev approach with k blocks. This requires the learner to somehow determine k from m, which is less clean but workable if b₀ is fixed.

2. **If probability amplification proof is too long**: Sorry the amplification lemma (1 sorry, well-isolated). The rest of the proof would be complete modulo this real analysis fact.

3. **If Fin arithmetic is painful**: Use `finProdFinEquiv` directly and avoid manual index arithmetic. Define `block j S i = S (finProdFinEquiv (j, i))` and prove properties via `finProdFinEquiv.symm`.

4. **If independence proof is hard**: The `iIndepFun_pi` + `indepFun_finset` path is clean but may need careful measurability proofs. Fallback: sorry the independence and note it's 1 sorry of clear mathematical content.

5. **NUCLEAR FALLBACK**: Factor the entire proof into 3 sorry'd lemmas:
   - `majority_vote_learner_exists` (construction)
   - `prob_amplification` (convergence)
   - `block_independence` (measure theory)
   And prove `boost_two_thirds_to_pac` from these 3 lemmas in ~15 LOC. Then attack each lemma separately.

---

## Summary of Resolutions

| UK | Status | Resolution |
|----|--------|------------|
| UK-1 | RESOLVED | Not needed. Fin has ⊤ MeasurableSpace. All functions measurable. |
| UK-2 | RESOLVED | `pi_map_piCongrLeft` takes plain Equiv, no MeasurableEquiv needed. |
| UK-3 | RESOLVED | `iIndepFun_pi` + `indepFun_finset` gives block independence directly. No nested pi. |
| UK-4 | RESOLVED | Column-major confirmed: (i,j) ↦ j + n*i. Block j = {j*n,...,j*n+n-1}. |
| UK-5 | RESOLVED | Not in Mathlib, not needed. `fun j i => S (finProdFinEquiv (j, i))` suffices. |
| UK-6 | RESOLVED | Both `Fin (k*m)` and `Fin k × Fin m` are valid Fintype index types for Measure.pi. |
| NEW-UK-1 | RESOLVED | Set L'.hypotheses = Set.univ, output_in_H trivial. |
| NEW-UK-2 | RESOLVED | IsProbabilityMeasure ⟹ SigmaFinite (standard Mathlib instance). |
| NEW-UK-3 | RESOLVED | isProbabilityMeasure_pi exists in Mathlib. |
