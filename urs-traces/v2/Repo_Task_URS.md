# Repo Task URS — FLT_Proofs Sorry Replacement Pipeline (v2, 2026-03-18)

## Task Identity

**Core mission:** Replace every `sorry` in FLT_Proofs with a correct, non-trivial proof.
Each sorry replacement is a γ-increment (discovery). Each obstruction diagnosis is a
Γ-increment (inquiry).

**Current state:** 0 errors, 31 sorrys. Library: `FLT_Proofs` (sole `@[default_target]`).

---

## A_task — Task Axioms (Non-Negotiable Invariants)

**TA₁:** Compilation monotonicity — `lake build` must succeed after every edit.
**TA₂:** A₄ — No sorry may prove a trivially true or vacuously satisfiable statement.
**TA₃:** A₅ — No sorry replacement may simplify the statement to make it provable.
**TA₄:** The MetaKernel is an agent on Γ (inquiry axis), not on γ (discovery axis).
**TA₅:** Every sorry has a tractability classification before attack.
**TA₆:** Break points are documented, not hidden.

---

## M_task — Task Mechanisms (5 Phases)

### Phase 1: Profiling (before attacking any sorry)

1. READ the sorry's type signature (hypotheses + conclusion)
2. CLASSIFY paradigm: PAC / Online / Gold / Universal / Cross-paradigm
3. IDENTIFY candidate proof methods from M₁-M₈
4. DERIVE metaprogram type (M-Bridge, M-Contrapositive, M-Pipeline, etc.)
5. CHECK upstream dependencies (does this sorry depend on other sorrys?)
6. CHECK BP blocking (is this sorry at a break point boundary?)
7. CLASSIFY ignorance quadrant (KU / UK / UU)
8. ASSESS tractability: Immediately Provable / Conditional / Blocked / Deep Structure

### Phase 2: World Model Construction

1. SELECT proof method (from Phase 1 candidates)
2. DECOMPOSE into substeps (sub-lemmas, Mathlib lemma lookup, construction steps)
3. VERIFY Mathlib API availability (grep Mathlib source, not guess)
4. COMPOSE into CompoundMechanism (seq / conj / branch / evalCustom)
5. ASSESS plausibility of completion

### Phase 3: Execution

1. WRITE CompoundMechanism specification
2. TRANSLATE to tactic proof (or term proof where natural)
3. EDIT the sorry in FLT_Proofs
4. CHECK A₅ violation (did the statement change? did content get dropped?)

### Phase 4: Verification

- Option A: `lake build` succeeds → check that no NEW sorry was introduced
- Option B: Proof compiles but uses axioms → check which axioms
- Option C: Proof fails → diagnose obstruction, record in Γ-ledger

### Phase 5: Recording

**On success:** Create γ-entry with proof summary, method used, Mathlib dependencies.
**On failure:** Create Γ-entry with obstruction classification:
  - KU-obstruction: known unknown (e.g., missing Mathlib API)
  - UK-obstruction: discovered unknown (e.g., type doesn't compose)
  - BP-obstruction: break point (record in BREAKS.md)

---

## R_task — Task Representations

### Sorry Inventory (current state — 2026-03-18)

#### Generalization.lean: 10 sorrys

| Sorry | Type | Tractability | Dependencies |
|-------|------|-------------|-------------|
| `ermLearn` | noncomputable def body | CONDITIONAL | iSup API for inf minimizer |
| `ermLearn_in_H` | theorem | CONDITIONAL | ermLearn definition |
| `trueError_eq_genError` | theorem | CONDITIONAL (KU₁) | Measurability hypotheses |
| `empiricalMeasureError_eq_empiricalError` | theorem | PROVABLE | Direct computation |
| `consistent_imp_zero_empiricalError` | theorem | PROVABLE | Direct from definitions |
| `erm_consistent_realizable` | theorem | CONDITIONAL (KU₆) | ERM minimizer existence |
| `vcdim_finite_imp_uc` | theorem (KEYSTONE) | CONDITIONAL | Growth function / covering |
| `uc_imp_pac` | theorem (KEYSTONE) | CONDITIONAL | ERM + UC → PACLearnable |
| `symmetrization_lemma` | theorem | BLOCKED (UK₃) | Measurability of sup over H |
| `pac_sample_complexity_pos` | theorem | PROVABLE | Nat.ceil positivity |

#### Theorem/PAC.lean: 9 sorrys

| Sorry | Type | Tractability | Dependencies |
|-------|------|-------------|-------------|
| `pac_imp_vcdim_finite` | theorem | CONDITIONAL | Contrapositive + construction |
| `vcdim_finite_imp_pac` | theorem | CONDITIONAL | vcdim_finite_imp_uc + uc_imp_pac |
| `pac_lower_bound` | theorem (A4 OK) | CONDITIONAL | Lower bound argument, Nat.ceil |
| `nfl_fixed_sample` | theorem (A4 OK) | CONDITIONAL (KU₁₉, KU₂₁) | Uniform measure construction |
| `sauer_shelah` | theorem | BLOCKED (UK_P2) | Shatters → Finset.Shatters bridge |
| `occam_algorithm` | theorem | CONDITIONAL | Concentration + finite H |
| `fundamental_rademacher` | theorem | BLOCKED | RademacherComplexity sorry-def |
| `fundamental_vc_compression` | theorem | CONDITIONAL | Compression → PAC direction |
| `fundamental_stability` | theorem | CONDITIONAL | Stability → gen bound |

#### Theorem/Separation.lean: 5 sorrys

| Sorry | Type | Tractability |
|-------|------|-------------|
| `pac_not_implies_online` | theorem | CONDITIONAL (KU₁₅) |
| `ex_not_implies_pac` | theorem | PROVABLE (construction) |
| `online_strictly_stronger_pac` | theorem | CONDITIONAL |
| `bc_strictly_stronger_ex` | theorem | PROVABLE (construction) |
| `vc_finite_ldim_infinite` | theorem | CONDITIONAL (KU₁₅) |

#### Theorem/Extended.lean: 5 sorrys

| Sorry | Type | Tractability |
|-------|------|-------------|
| `universal_trichotomy` | theorem | DEEP STRUCTURE |
| `natarajan_characterization` | theorem | CONDITIONAL |
| `ds_characterization` | theorem | CONDITIONAL |
| `compression_conjecture` | theorem | DEEP STRUCTURE (open problem) |
| `multiclass_pac_characterization` | theorem | CONDITIONAL |

#### Rademacher.lean: 1 sorry

| Sorry | Type | Tractability |
|-------|------|-------------|
| `RademacherComplexity` | noncomputable def body | CONDITIONAL (needs distribution + sample size params) |

#### Bridge.lean: 1 sorry

| Sorry | Type | Tractability |
|-------|------|-------------|
| `shatters_bridge` | theorem | BLOCKED (UK_P2: Shatters → Finset.Shatters) |

### External Dependencies (Updated)

| ID | Dependency | Status (v2) |
|----|-----------|-------------|
| K₄ | Hoeffding/concentration lemmas | **DISSOLVED** — Mathlib has `one_sub_le_exp_neg`, `one_sub_div_pow_le_exp_neg` |
| K₄' | Missing infrastructure layer | **RESOLVED** — TrueError, UC, symmetrization added |
| UK_P2 | Shatters → Finset.Shatters bridge | OPEN — needed for sauer_shelah |
| UK₃ | Measurability of sup over uncountable H | OPEN — blocks symmetrization |

---

## T_task — Task Traces

### Attack Order (Updated for v2)

**Wave 1 (COMPLETED):** γ₁-γ₃, γ₆ — immediately provable sorrys. All closed.

**Wave 1.5 (COMPLETED):** Online.lean M-DefinitionRepair. All 10 theorems compiled.

**Wave 2 (ACTIVE — infrastructure-enabled):**
Priority order based on sorry DAG dependencies:
1. `empiricalMeasureError_eq_empiricalError` — direct computation
2. `consistent_imp_zero_empiricalError` — direct from definitions
3. `pac_sample_complexity_pos` — Nat.ceil positivity
4. `trueError_eq_genError` — bridge theorem (KU₁ measurability)
5. `erm_consistent_realizable` — ERM minimizer (KU₆)

**Wave 3 (KEYSTONE — sorry DAG critical path):**
1. `vcdim_finite_imp_uc` — VCDim finite → uniform convergence (KEYSTONE)
2. `uc_imp_pac` — uniform convergence → PACLearnable (KEYSTONE)
3. `pac_imp_vcdim_finite` — contrapositive direction

**Wave 4 (SEPARATIONS + BOUNDS):**
1. `ex_not_implies_pac` — construction (provable)
2. `bc_strictly_stronger_ex` — construction (provable)
3. `pac_not_implies_online` — needs VCDim < ∞, Ldim = ∞ example (KU₁₅)
4. `pac_lower_bound` — lower bound argument
5. `nfl_fixed_sample` — uniform measure construction (KU₁₉, KU₂₁)
6. `occam_algorithm` — finite H + concentration

**Wave 5 (ASSEMBLY):**
1. `sauer_shelah` — needs UK_P2 bridge
2. `fundamental_vc_compression` — compression ↔ PAC
3. `fundamental_stability` — stability → gen bound
4. `fundamental_rademacher` — needs RademacherComplexity def body
5. Extended theorems (natarajan, ds, multiclass)

**Wave 6 (DEEP STRUCTURE):**
1. `universal_trichotomy` — needs VCL tree analysis
2. `compression_conjecture` — open mathematical problem
3. `symmetrization_lemma` — needs UK₃ (measurability of sup)

### Session Protocol

1. Read this URS and `Axioms/v2/TASK_URS.md` at session start
2. Check which wave is active
3. Attack sorrys in wave order (dependencies first)
4. After each sorry: update sorry inventory, update wave status
5. If blocked: create Γ-entry, move to next attackable sorry
6. At session end: update sorry count, update wave status

---

## γ — Discovery Ledger (Completed, excerpts)

| ID | Content | Session |
|----|---------|---------|
| γ₁-γ₃ | VCDim/NFL basic proofs | 2026-03-16 |
| γ₆ | Bridge.lean clear | 2026-03-16 |
| γ₁₁ | gold_theorem (200 lines) | 2026-03-17 |
| γ₁₂-γ₂₀ | Online.lean (10 theorems) | 2026-03-17 |
| γ₂₁ | mind_change_characterization | 2026-03-17 |
| γ₂₂-γ₂₆ | Bridge/Complexity batch | 2026-03-17 |
| γ₂₇-γ₃₁ | Computation.lean (5 closed) | 2026-03-17 |
| γ₃₂-γ₃₄ | MetaKernel WorldModel | 2026-03-17 |
| γ₃₅ | Γ₂₇ resolved (BddAbove) | 2026-03-18 |
| γ₃₆ | PAC infrastructure layer | 2026-03-18 |
| γ₃₇-γ₃₈ | A4 repairs (pac_lower_bound, nfl) | 2026-03-18 |
| γ₃₉ | vc_characterization factored | 2026-03-18 |

## Γ — Inquiry Ledger (Recent)

| ID | Content | Status |
|----|---------|--------|
| Γ₂₇ | VCDim_embed_ordinal blocked (Ordinal BddAbove) | **RESOLVED** (γ₃₅) |
| Γ₃₁ | K4 obstruction diagnosis | **DISSOLVED** (Mathlib has the APIs) |
| Γ₃₂ | BP₈ discovery (ENNReal/ℝ error joint) | OPEN |
| Γ₃₃ | A4 violations discovered (pac_lower_bound, nfl) | **RESOLVED** (γ₃₇-γ₃₈) |
| Γ₃₄ | Sorry DAG dependency structure identified | OPEN (UK_P1) |
