# Claude's Task URS — Metaprogram Synthesis Protocol

## Task Identity

Claude's task in this project is **metaprogram synthesis assistance**. Claude does NOT prove theorems directly. Claude helps the MetaKernel (Repo) discover the metaprograms (world models) that, when executed, replace sorrys in `KernelSnapshot/`.

The operational loop:

```
1. READ Repo_Noological_URS → identify next sorry target
2. TRANSFER ignorance: Repo's K/U for that sorry → Claude's K/U for synthesizing a metaprogram
3. SELECT mechanism (CM₁-CM₆) from Claude_Noological_URS
4. SYNTHESIZE metaprogram (CompoundMechanism or evalCustom)
5. WRITE metaprogram to Discovery.lean or WorldModel/
6. EXECUTE metaprogram: write proof into KernelSnapshot/
7. VERIFY: compile or type-check
8. RECORD: update both Repo and Claude traces
```

## Pre-Flight Protocol (MANDATORY — before every Write/Edit)

### Gate 0: Path Invariant Check
```
TARGET FILE is in MetaKernel/KernelSnapshot/ ?  → proceed
TARGET FILE is in LimitsOfLearning/             ?  → STOP. Wrong path. (CNA₃)
TARGET FILE is in MetaKernel/*.lean             ?  → proceed (metaprogram engine)
TARGET FILE is elsewhere                        ?  → STOP. Check task scope.
```

### Gate 1: A₅ Anti-Simplification Check
Before EVERY write, answer explicitly:
- Am I about to drop content to make things compile? → STOP
- Am I falling back to a simpler version of the problem? → STOP
- Am I using `sorry`, `| _ => throwError "..."`, or equivalent content drops? → STOP (unless documenting an obstruction)
- Am I making strategy selection shape-homogeneous when GoalProfile has more structure? → STOP

If A₅ violation detected: **expand R** (investigate the API obstacle, discover missing structure, add new KUs). The answer is MORE structure, not less.

### Gate 2: Task URS Skill Invocation
Call `task-urs-typing-derivation` for any new Lean4 type, def, structure, class, instance, or theorem statement. This prevents type-homogeneity (CNA₁).

### Gate 3: Noological URS Skill Invocation
Call `anthropic-skills:noological-urs` to maintain Claude's K/U partition. State explicitly:
- What's in KK for this specific write
- What's in KU (open questions)
- What's in UK (unverified pattern-matches)
- Tractability classification: IMMEDIATELY SYNTHESIZABLE | CONDITIONALLY SYNTHESIZABLE | BLOCKED

### Gate 4: Metaprogram-First Check (CNA₄)
Am I about to write a tactic proof directly into KernelSnapshot?
- If YES without a prior metaprogram in Discovery.lean or WorldModel/ → STOP
- The metaprogram must exist FIRST, then the proof is its execution

Exception: trivial proofs (exact, rfl, simp) that are obviously instances of M-Construction don't need a separate metaprogram file entry. But the metaprogram TYPE must still be identified.

### Gate 5: Measurement Gate (NEW — WorldModel/MeasuredTactic.lean)
For non-trivial proofs, use `measured_proof` wrapper which enforces:
- `pl_gate`: non-triviality check (conclusion is not trivially true)
- `coh_gate`: well-typedness check (all terms type-check)
- `inv_gate`: stability check (proof doesn't depend on sorry ordering)
- `comp_gate`: sorry tracking (count before/after)

### Gate 6: Prior-Art Check (NEW — WorldModel/PriorArt.lean)
Before attacking a K₄-blocked sorry, check:
- `findRelevantTheorems` against Yuanhe Z traces (concentration inequalities)
- `extractStrategyChain` from Google formal-ml traces (PAC/VC strategies)
- `minAdaptationCost` to estimate translation effort

### Gate 7: Feedback Loop (NEW — WorldModel/Feedback.lean)
After a failed sorry attack:
- `TraceAnalysis` extracts patterns from the failed attempt
- `StrategyPatch` generates: promote/demote/addConstraint/coordinatedStrategy/usePriorArt
- `feedbackLoop` re-attempts with patched strategy
- `feedback_proof` tactic wraps the full loop

## Sorry Selection Protocol

### Priority Ordering

Select the next sorry to attack based on:

1. **Dependency-free sorrys first** — sorrys that don't depend on other sorrys
2. **IMMEDIATELY PROVABLE sorrys** — where all APIs are Verified and method is known
3. **Cluster attacks** — sorrys that share a method class (batch M-Bridge, batch M-Contrapositive)
4. **Blocked sorrys last** — document the obstruction and move on

### Current Sorry Triage (as of 2026-03-16)

**Tier 1 — IMMEDIATELY PROVABLE** (dependency-free, method known):
- `vcdim_to_ordinal_vcdim` (Bridge.lean) — M-BridgeLift, OBSTRUCTED by witness extraction
  - Obstruction: WithTop.iSup witness API (KU₂)
  - Action: search Mathlib for alternative proof architecture

**Tier 2 — CONDITIONALLY PROVABLE** (method known, APIs need verification):
- `pac_imp_vcdim_finite` — M-Contrapositive (deep probabilistic argument)
- `sauer_shelah_quantitative` — M-Bridge (needs Finset.Shatters bridge verification)
- `nfl_fixed_sample` — M-Pipeline (counting argument, should be tractable)
- Separation theorems — M-Diagonalization (batch of 7)

**Tier 3 — BLOCKED** (missing external dependency):
- `vcdim_finite_imp_pac` — needs Hoeffding (K₄)
- `occam_algorithm` — needs Hoeffding (K₄)
- `fundamental_vc_compression` — needs compression scheme formalization
- `fundamental_rademacher` — needs Rademacher complexity tools

**Tier 4 — DEEP STRUCTURE NEEDED**:
- `vc_characterization` — M-Conjunction of Tier 2 + Tier 3 results
- `fundamental_theorem` — M-Conjunction of everything
- ~~Computation.lean sorrys~~ — **CLOSED** (γ₂₇-γ₃₁, all 5 resolved)

**Tier 5 — PRIOR-ART GUIDED (NEW)**:
- K₄-blocked sorrys may be unblockable via Yuanhe Z's `subGaussian_finite_max_bound` (KU₉)
- PAC bound strategy translatable from Google formal-ml via PriorArtTheorem traces (KU₁₀)
- Use `feedback_proof` tactic for iterative sorry attacks (KU₁₁)

## Ignorance Transfer Protocol

The core operation: reading the Repo's ignorance profile for a sorry and mapping it to Claude's own ignorance profile for the synthesis problem.

```
Input:  Repo_Noological_URS.sorry_profile(target)
        → { paradigm, method_candidates, dependencies, bp_blocked, ignorance_class }

Process: For each field, Claude asks:
         - method_candidates → Do I (Claude) know how to instantiate this as a CompoundMechanism? (CM₁)
         - dependencies → Are dependencies resolved in KernelSnapshot? (read file)
         - bp_blocked → Is this a SubstrateLimit for Claude or just for the Repo's current R?
         - ignorance_class → Map:
             KU_standard     → KK_Claude (Claude can pattern-instantiate)
             KU_composite    → KU_Claude (Claude needs to discover the composition)
             KU_bp_blocked   → UK_Claude or UU_Claude (depends on BP nature)
             UK_mathlib      → UK_Claude (Claude must search, not guess — CA₅)
             UK_literature   → KK_Claude or KU_Claude (depends on training coverage)
             UU_undecidable  → UU_Claude (escalate to user)

Output: Claude_synthesis_profile := {
          target, mechanism : CM₁-CM₆,
          api_confidence : Verified | PatternMatched | Unknown,
          obstruction : Option Obstruction,
          tractability : IMMEDIATE | CONDITIONAL | BLOCKED
        }
```

## Metaprogram Synthesis Templates

### Template: M-Bridge Synthesis
```
1. Identify source def (ours) and target def (Mathlib)
2. Search Mathlib for the target def signature (CM₂: API Discovery)
3. Construct mediator bijection between the two representations
4. Write CompoundMechanism:
   seq [applyLemma "iff_intro",
        seq [introAssumption, applyLemma "<forward_lemma>"],
        seq [introAssumption, applyLemma "<backward_lemma>"]]
5. Execute: write tactic proof into KernelSnapshot
```

### Template: M-Contrapositive Synthesis
```
1. Negate the goal: ¬P → need to assume P and derive ⊥
2. Identify the contradiction source (often: finite < infinite, or type mismatch)
3. Construct the witness/intermediate result that bridges assumption to contradiction
4. Write CompoundMechanism:
   seq [introAssumption,
        applyLemma "<key_intermediate>",
        applyLemma "<rewrite_to_contradiction>",
        closeContradiction]
5. Execute: write tactic proof into KernelSnapshot
```

### Template: M-Pipeline Synthesis
```
1. Decompose the goal into sequential stages:
   Bound → Concentrate → Construct → Compose
2. For each stage, identify the Mathlib API (CM₂)
3. Verify API existence and signature compatibility (Coh check)
4. Write CompoundMechanism:
   seq [stage₁_mechanism, stage₂_mechanism, ..., stageₙ_mechanism]
5. Execute: write tactic proof into KernelSnapshot
```

### Template: M-Conjunction Synthesis
```
1. Identify the component results needed (all must be proved or sorry-with-plan)
2. Check dependency graph: are all components available?
3. If not: return BLOCKED with dependency list
4. If yes: assemble via
   conj [component₁_proof, component₂_proof, ..., componentₙ_proof]
5. Execute: write combined proof into KernelSnapshot
```

### Template: M-Construction Synthesis
```
1. Look up the mathematical definition from literature (CM₂ variant: literature search)
2. Translate the mathematical object into Lean4 term-mode expression
3. Verify: does the term have the right type? (may need type annotation)
4. Write as: exact ⟨witness₁, witness₂, ..., property_proof⟩
5. Execute: write term into KernelSnapshot
```

## Trace Protocol

After every sorry attack (success or failure), record:

### In Repo_Noological_URS.md (Comp tracking):
- Update sorry count
- If success: add γ-entry
- If failure: add Γ-entry with obstruction diagnosis
- If new constraint: add to V-table

### In Claude_Noological_URS.md (K/U update):
- Move items between KK/KU/UK/UU based on what was learned
- If new CNA discovered: append to CNA table
- If API confidence changed: update APIConfidence entries

### In Discovery.lean (metaprogram record):
- Add the synthesized CompoundMechanism/evalCustom strategy
- Document the metaprogram type and target sorry

## KU Discovery Section: Lattice Type Expansion (Natural → WithBot (WithTop ℕ))

### Is this lattice formalization trivial or a genuine addition?

**Arguments for GENUINE contribution:**
1. No existing Lean4/Coq/Isabelle formalization of Littlestone dimension exists (first-in-field)
2. `WithBot (WithTop ℕ)` is NOT the obvious choice — papers use ℤ ∪ {∞} or ℕ ∪ {∞} with ad-hoc conventions
3. The type dissolves a genuine proof obstruction (Γ₂₁) that would require an ad-hoc SOA patch otherwise
4. `CompleteLattice` structure enables `iSup₂` directly — the most natural definition of Littlestone dimension
5. The type ENCODES the mathematical invariant at the type level: Ldim ∈ {-1} ∪ ℕ ∪ {∞}. No runtime guards needed.
6. The ℤ alternative was rejected on structural grounds (no CompleteLattice, ring structure is noise) — this rejection IS a contribution to the formalization methodology

**Arguments for TRIVIAL:**
1. The mathematical content (Ldim(∅) = -1) is well-known
2. `WithBot` is a standard Mathlib construction
3. The SOA fix follows mechanically from the type change

**Verdict: η ≈ 0.6** — Non-trivial as FORMALIZATION TECHNIQUE, trivial as mathematical content. The contribution is in TYPE DESIGN: making implicit conventions explicit at the type level, where the type system enforces invariants that papers leave to convention. This is exactly what formal verification adds to mathematics.

### New tactics and methods enabled by the lattice structure

| New capability | Source | Enables |
|---|---|---|
| `iSup₂` on `WithBot (WithTop ℕ)` | `CompleteLattice` instance | Natural LittlestoneDim definition without workarounds |
| `⊥ < ↑↑0` strict comparison | `WithBot.bot_lt_coe` | SOA correctness at d=0 (dissolves Γ₂₁) |
| `iSup₂_le` + `le_iSup₂_of_le` | `CompleteLattice` | All monotonicity/bound proofs carry over from WithTop ℕ |
| `bot_le : ⊥ ≤ a` for all a | `OrderBot` | Empty-class cases become trivial |
| `iSup₂` over empty set = `⊥` | `CompleteLattice` + `simp` | Ldim(∅) = ⊥ is automatic |
| 3-way case analysis on `WithBot (WithTop ℕ)` | `WithBot.cases`/pattern matching | Clean separation of ⊥/finite/∞ cases in all theorems |
| `sInf` and `sSup` | `CompleteLattice` | Potential dual formulation of LittlestoneDim (UK₇ in Repo) |

### New premises that become plausible (KU → hypotheses)

| Hypothesis | Plausibility | Evidence needed |
|---|---|---|
| `backward_direction` provable without ad-hoc SOA patch | HIGH | Path B dissolves d=0. M-Potential for d≥1 already proved. |
| `optimal_mistake_bound_eq_ldim` statable with coercion `↑(OptimalMistakeBound) = LittlestoneDim` for C.Nonempty | HIGH | Types match after lifting OptimalMistakeBound into WithBot |
| All Online.lean sorrys closable in ONE session | MEDIUM | Depends on backward_direction's M-Potential proof compiling |
| VCDim needs identical WithBot treatment (UK₉) | LOW-MEDIUM | Need to check if VCDim proofs have analogous empty-class issues |
| Lattice-theoretic minimax theorem for online learning | SPECULATIVE | Would reframe fundamental theorem as sSup = sInf in the lattice |

### New questions that become askable (UU → UK/KU transitions)

1. **UU → KU:** "What is Ldim(∅)?" was previously UU (undefined/convention-dependent). Now KU: Ldim(∅) = ⊥, provable by `simp`.
2. **UU → UK:** "Can SOA be proved optimal without case-splitting on d?" was UU. Now UK: the CompleteLattice's well-order enables induction on the lattice value directly, potentially eliminating the d=0/d≥1 split.
3. **UU → KU:** "What bridge connects OptimalMistakeBound to LittlestoneDim?" was UU (types didn't match). Now KU₁₁: the coercion `↑ : WithTop ℕ → WithBot (WithTop ℕ)` is the bridge.
4. **UU → UK:** "Is there a version of Littlestone characterization for empty classes?" was meaningless before. Now UK: for empty C, Ldim = ⊥ < ⊤ and OnlineLearnable holds vacuously, so the characterization holds with the understanding that ⊥ < ⊤.

## Error Recovery Protocol

### Compilation Error After Proof Write
1. READ the error message (CM₃: Obstruction Diagnosis)
2. CLASSIFY: type mismatch | unknown identifier | universe error | tactic failure
3. If unknown identifier → likely CA₅ (wrong API name). Search Mathlib. Do NOT guess a fix.
4. If type mismatch → read both expected and actual types. This is often a UK_Claude that becomes KK_Claude.
5. If universe error → document as SubstrateLimit. May need user help.
6. If tactic failure → the metaprogram is wrong, not just the execution. Return to synthesis step.

### Context Compression Recovery
1. Re-read all 4 URS files in `MetaKernel/URS/`
2. Re-read `MetaKernel/AGENT.md` and `MetaKernel/TASK_URS.md` (legacy canonical versions)
3. Check sorry inventory: what's been proved since last session?
4. Restore K/U partition from Claude_Noological_URS.md

This is Claude's **continuity mechanism** across context compressions. The URS files ARE Claude's persistent memory for this project.
