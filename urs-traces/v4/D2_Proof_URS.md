# D2 Proof Agent URS — Close 3 NFL Sorrys

## Measurement State (Pre-Proof)

### Pl (Plausibility) = 0.75
The 3 sorrys share a common mathematical core: double-counting + pigeonhole on
finite product types, then measure bridge to Measure.pi. The `per_sample` lemma
(adversarial construction) is PROVED. The infrastructure bridge lemmas
(`uniformMeasure_singleton`, `pi_uniformMeasure_singleton`, `pi_uniformMeasure_finset`)
are PROVED and in the codebase. The combinatorial core (nfl_core, disagreement_sum_eq,
exists_many_disagreements) is sorry-free.

Risk: Gamma_91 identified a non-measurability blocking obstacle. The set
`goodX = {xs : Fin m -> X | D{disagree} <= 1/4}` is NOT measurable without
`MeasurableSingletonClass X`. The D2-NFL agent identified the COMPLEMENT approach
as resolution: work with `goodX^c` using `le_map_apply` (correct direction for
lower bounds on complements).

### Coh (Coherence) = 0.55
The proof composes 4 layers:
1. Shattered set extraction (from VCDim) — PROVED
2. Adversarial construction per sample (per_sample) — PROVED
3. Double-counting + pigeonhole (combinatorial core) — needs writing
4. Measure bridge (counting -> Measure.pi) — bridge lemmas PROVED but composition needs Gamma_91 workaround

HC at layer 3-4 joint = 0.6: The double-counting produces a COUNTING bound
`2 * |{good xs}| <= card(Fin m -> T)`. Converting this to `Measure.pi D goodX <= 1/2`
requires the pushforward bridge `D = D_sub.map val` where `D_sub = uniformMeasure T`.
The non-measurability of `goodX` in `Fin m -> X` means we can't use `MeasurableEmbedding.map_apply`
directly. The complement approach adds ~20 LOC of ENNReal arithmetic.

HC at layer 2-3 joint = 0.2: The per_sample lemma gives an adversarial c for EACH xs.
The double-counting needs to go from "for each xs, exists bad c" to "exists c bad
for many xs". This is a Fubini/averaging argument that's standard but needs careful
formalization over `Fin m -> T` with `Finset.sum_comm`.

### Inv (Invariance) = 0.50
Two proof routes for the measure bridge:
- Route A (Direct): `pi_uniformMeasure_finset` on the GOOD set -> bound -> complement
- Route B (Complement): `le_map_apply` on the BAD set complement -> ENNReal subtraction

Route B (complement) was identified by D2-NFL agent as more robust (avoids
non-measurability issue). Both routes use the same infrastructure.

Counting core has one route: Finset.sum_comm + pigeonhole. No alternative.

### Comp (Completeness) = 0.30
Of the estimated ~260 total LOC for all 3 sorrys:
- 0 LOC written for the sorrys themselves
- ~20 LOC bridge infrastructure PROVED and in codebase
- ~30 LOC per_sample + adversarial construction PROVED
- ~210 LOC remaining (counting core + measure bridge + edge cases, x3 sorrys)

## Obstruction Analysis

### HC_1: Non-measurability of goodX in Fin m -> X (0.6) — Gamma_91
The set `{xs : Fin m -> X | D{x | h x != c x} <= eps}` for h = L.learn(xs) is
NOT measurable in `MeasurableSpace.pi` without `MeasurableSingletonClass X`.

RESOLUTION (complement approach):
```
-- Instead of bounding mu(goodX) directly:
-- 1. Show mu(goodX^c) >= 1/2 via le_map_apply (correct direction for complements)
-- 2. Then mu(goodX) <= 1 - mu(goodX^c) <= 1 - 1/2 = 1/2
-- 3. mu(goodX) + mu(goodX^c) >= mu(univ) = 1 (always true, even for non-measurable sets)
-- 4. So mu(goodX) <= 1 - 1/2 = 1/2 < 6/7 = 1 - 1/7
```

Key: `le_map_apply` gives `mu(f^{-1} S) <= mu.map f S` — the LOWER bound on
the preimage, which gives an UPPER bound on the complement. This avoids needing
measurability of the original set.

### HC_2: Double-counting composition (0.3)
The counting argument:
```
sum_f sum_xs [good(f, xs)] = sum_xs sum_f [good(f, xs)]
                            <= card(Fin m -> T) * 2^{d-1}
```
where `good(f, xs)` means "error of c_f on xs <= eps under D = uniform on T".

The pairing argument: for fixed xs, pair f_unseen with !f_unseen. Within each pair,
at most one has <= d/4 disagreements. So #{good f for fixed xs} <= 2^{d-1}.

This requires:
- `Finset.sum_comm` for double sum exchange
- Pairing on `Fin unseen -> Bool` via `Bool.not`
- Cardinality argument: `2^{d-1}` bound per xs

### HC_3: pi_uniformMeasure_finset composition with pushforward (0.4)
The bridge lemmas work on `Fin m -> T` (discrete product). But the sorrys work on
`Fin m -> X` (general MeasurableSpace). The connection goes through:
```
D = D_sub.map val   where D_sub = uniformMeasure T, val = Subtype.val : T -> X
Measure.pi D = (Measure.pi D_sub).map valProd   where valProd xs i = (xs i).val
```
The `pi_map_pi` lemma gives this. Then `pi_uniformMeasure_finset` applies on the
subtype side.

## Inquiry State

### KK (Known)
- `uniformMeasure_singleton`, `pi_uniformMeasure_singleton`, `pi_uniformMeasure_finset` PROVED
- `per_sample` adversarial construction PROVED for all 3 sorrys
- `nfl_core` PROVED for finite domains
- `disagreement_sum_eq`, `exists_many_disagreements` PROVED
- `shatters_realize`, `shatters_hard_labeling` PROVED
- `Fintype.card (Fin m -> T) = card T ^ m` (Mathlib, already used in codebase)
- `le_map_apply` gives mu(f^{-1} S) <= mu.map f S (Measure/Map.lean)
- Complement approach resolves Gamma_91 non-measurability

### KU (Articulated unknowns)
- CKU_1: Does `pi_map_pi` compose with `valProd` to give `Measure.pi D` from `Measure.pi D_sub`?
- CKU_2: Can the pairing argument (f_unseen vs !f_unseen) be formalized via `Equiv.boolProd`?
- CKU_3: Does `Finset.sum_comm` have the right type for our double sum over `(Fin m -> T) x (T -> Bool)`?
- CKU_4: Is `2^{d-1}` the correct bound per xs? The pairing gives: for each equivalence class
  of labelings agreeing on range(xs), at most half have <= d/4 unseen disagreements.
  #{classes} = 2^m (labelings of m seen points). Per class: at most 2^{d-m-1} good out of 2^{d-m}.
  Total: 2^m * 2^{d-m-1} = 2^{d-1}. Yes, correct.
- CKU_5: For sorry #6 (vcdim_infinite_not_pac): substep A and substep B are already factored.
  Can substep B use the same complement approach as sorry #3?

### UK (Pressures)
- UK_1: Whether the 3 sorrys can share a common helper lemma (the measure bridge)
  or whether each needs its own version due to different quantifier structures
- UK_2: Whether `le_map_apply` is sufficient for the complement approach or whether
  we need `Measure.map_apply` with a measurability proof
- UK_3: Whether the edge case `d = 0` (no shattered set) needs separate handling

### UU (Boundary)
- UU_1: Whether a purely combinatorial proof (avoiding Measure.pi entirely) exists
  by working on the Fintype product `Fin m -> T` throughout and only converting to
  `Fin m -> X` at the very end via a single pushforward step

## Discovery Task
Close all 3 NFL sorrys:
1. pac_lower_bound_core (Generalization:1893) — the main NFL lower bound
2. pac_lower_bound_member (Generalization:2423) — routes through #1
3. vcdim_infinite_not_pac (Generalization:2863) — substep A + substep B

Recommended order: #3 substep B first (pure measure bridge, tests the complement approach),
then #3 substep A (combinatorial pigeonhole), then #1 (full NFL), then #2 (wrapper).

## Protocol
1. Read all 3 sorry contexts in Generalization.lean
2. Read the bridge lemmas (uniformMeasure_singleton etc.) to understand interfaces
3. Attempt #3 substep B (measure bridge) using complement approach
4. If complement approach works: apply to #1 and #2
5. Build after every change
6. If measurability blocks: document the exact obstacle
