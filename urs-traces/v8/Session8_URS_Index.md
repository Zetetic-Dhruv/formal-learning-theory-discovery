---
session: 8
date: 2026-03-25 to 2026-03-26
total_urs_count: 22
sorry_closed: 25+
files_touched: Extended.lean, Separation.lean, PAC.lean
---

# Session 8 URS Index

## Overview

Session 8 closed all remaining sorrys across three major proof tasks:
- **FP5** (advice_elimination): 3 sorrys -> 0 via GoodPair architecture + Nat.unpair bridge
- **FP4** (boost_two_thirds_to_pac): Full 7/12-fraction boosting with 9 helper lemmas + Phase 3 assembly
- **FP6** (fundamental_theorem conjunct 4): Trivially-true statement -> quantitative sandwich

## URS Documents

### FP5: advice_elimination (Extended.lean)

| # | File | Task | Target | Status |
|---|------|------|--------|--------|
| 1 | `Session8_FP5_advice_elimination_URS.md` | FP5 | advice_elimination (3 sorrys -> 0), GoodPair architecture | CLOSED |
| 2 | `Session8_S1_MeasurableSet_GoodTrain_URS.md` | S1 | UK_5: MeasurableSet GoodTrain | CLOSED |
| 3 | `Session8_S2_MeasurableSet_BadVal_URS.md` | S2 | UK_6: MeasurableSet BadVal | CLOSED |
| 4 | `Session8_S3_Hoeffding_arithmetic_URS.md` | S3 | UK_2: Hoeffding arithmetic | CLOSED |
| 5 | `Session8_S4_Final_calc_Nat_unpair_URS.md` | S4 | UK_7: Final calc / Nat.unpair cast | CLOSED |
| 6 | `Session8_S5_Route_E_set_equality_bridge_URS.md` | S5 | Route E: Set-equality bridge for Nat.unpair binder cast | CLOSED |

FP5 had 4 URS versions (v1-v4) tracking the iterative refinement of the GoodPair transport architecture. The main URS file contains all versions. S1-S4 were sub-tasks dispatched to parallel agents. S5 was the final Fin-matching bridge (Route E) that closed the last sorry.

### FP6: fundamental_theorem conjunct 4 (PAC.lean)

| # | File | Task | Target | Status |
|---|------|------|--------|--------|
| 7 | `Session8_FP6_conjunct4_upgrade_URS.md` | FP6 | Conjunct 4 upgrade: trivial -> sandwich | CLOSED |

Replaced trivially-true `mf epsilon delta >= 1` with quantitative sandwich: `sample_complexity_upper_of_pac_witness` + `pac_sample_complexity_sandwich`.

### FP4: boost_two_thirds_to_pac (Separation.lean)

| # | File | Task | Target | Status |
|---|------|------|--------|--------|
| 8 | `Session8_FP4_boost_two_thirds_to_pac_URS.md` | FP4 | Full 7/12-fraction boosting architecture | CLOSED |
| 9 | `Session8_FP4_Phase1_scaffolding_URS.md` | FP4-Phase1 | Scaffolding + interface change | CLOSED |
| 10 | `Session8_T0_measurableSet_goodBlock_A_URS.md` | T0 | measurableSet_goodBlock_A (shared helper) | CLOSED |
| 11 | `Session8_T2_goodBlockEvent_measurable_URS.md` | T2 | goodBlockEvent_measurable | CLOSED |
| 12 | `Session8_T3_map_block_extract_eq_pi_URS.md` | T3 | map_block_extract_eq_pi | CLOSED |
| 13 | `Session8_T4_goodBlockEvent_prob_ge_two_thirds_URS.md` | T4 | goodBlockEvent_prob_ge_two_thirds | CLOSED |
| 14 | `Session8_T5_iIndepSet_goodBlockEvents_URS.md` | T5 | iIndepSet_goodBlockEvents | CLOSED |
| 15 | `Session8_T6_chebyshev_seven_twelfths_bound_URS.md` | T6 | chebyshev_seven_twelfths_bound | CLOSED |
| 16 | `Session8_T7_majority_error_le_seven_rate_URS.md` | T7 | majority_error_le_seven_rate_of_good_fraction | CLOSED |
| 17 | `Session8_T8_boosted_sample_error_le_URS.md` | T8 | boosted_sample_error_le_of_good_blocks | CLOSED |
| 18 | `Session8_P3a_mf_constant_fix_URS.md` | P3a | mf constant fix (9/delta -> 36/delta) | CLOSED |
| 19 | `Session8_P3b_Phase3_body_URS.md` | P3b | Phase 3 body (everything except hlearn_unfold) | CLOSED |
| 20 | `Session8_P3c_hlearn_unfold_congrArg_URS.md` | P3c | hlearn_unfold congrArg ladder | CLOSED |
| 21 | `Session8_S9_hlearn_unfold_Fin_bridge_URS.md` | S9 | hlearn_unfold Fin bridge (earlier attempt) | BLOCKED (superseded by P3c) |
| 22 | `Session8_S10_fix_hlearn_unfold_URS.md` | S10 | Fix hlearn_unfold compile error | BLOCKED (superseded by P3c) |

FP4 was decomposed into 3 phases: Phase 1 (scaffolding), Phase 2 (9 helper lemmas T0-T8), Phase 3 (assembly: P3a-P3c). T1 (learn_measurable_fixed) was proved inline by the Phase 1 agent. S9 and S10 were earlier attempts at hlearn_unfold before a file reset necessitated P3c.

## Dependency Graph (FP4)

```
T0 (measurableSet_goodBlock_A)
  |
  +-- T2 (goodBlockEvent_measurable) -- depends on T0
  |     |
  |     +-- T5 (iIndepSet_goodBlockEvents) -- depends on T2, T0
  |
  +-- T4 (goodBlockEvent_prob_ge_two_thirds) -- depends on T0, T3

T3 (map_block_extract_eq_pi) -- standalone
  |
  +-- T4 (see above)

T6 (chebyshev_seven_twelfths_bound) -- standalone, mirrors chebyshev_majority_bound

T7 (majority_error_le_seven_rate_of_good_fraction) -- standalone

T8 (boosted_sample_error_le_of_good_blocks) -- depends on T1, T7

Phase 3: P3a -> P3b -> P3c (sequential)
  P3a: mf constant fix
  P3b: full proof body (uses T2, T4, T5, T6, T8)
  P3c: hlearn_unfold (Fin index bridge)
```

## Key Patterns

1. **Measurability chain** (T0 -> T2 -> T5): measurableSet_goodBlock_A provides the base set measurability, T2 lifts it through block_extract preimages, T5 converts iIndepFun to iIndepSet via these preimages.

2. **Pushforward identity** (T3 -> T4): map_block_extract_eq_pi shows the pushforward of D^{k*n} under block extraction equals D^n, enabling T4 to reduce the marginal probability to huniv.

3. **Concentration + Markov** (T6 + T7 -> T8 -> P3b): Chebyshev concentration (T6) gives high probability of enough good blocks; majority error bound (T7) gives that enough good blocks implies low error; T8 wraps T7 for the boosted learner; P3b composes all.

4. **Fin binder mismatch** (S5, S9, S10, P3c): Recurring pattern where `Nat.unpair (Nat.pair m1 m2)` in learner lambda binder types does not definitionally reduce, requiring set-equality bridges (S5) or congrArg ladders (P3c).
