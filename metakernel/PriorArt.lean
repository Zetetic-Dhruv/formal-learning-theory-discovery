/-
  MetaKernel.WorldModel.PriorArt — External libraries as typed traces

  A PriorArt trace captures what we KNOW from an external library:
  - Theorem statements (as strings — cross-version portable)
  - Proof strategies (decomposed into method sequences)
  - Type mappings (how their types correspond to ours)
  - Obstruction analysis (what they DON'T have that we need)

  Two libraries consumed:
  1. Yuanhe Z (lean-stat-learning-theory) — Lean4, 34,892 lines, 0 sorry
     Concentration inequalities: Efron-Stein, sub-Gaussian, Dudley, covering numbers
  2. Google formal-ml — Lean3, 36,221 lines, 0 sorry
     PAC learning: VC dimension, Sauer-Shelah, Hoeffding, ERM generalization

  These traces are WORLD MODELS: structured predictions about what proofs exist
  and how they compose. The MetaKernel agent consumes them to plan sorry closure.
-/

import Lean

namespace MetaKernel.WorldModel

/-! ## Proof Strategy Atoms: The vocabulary for describing how a proof works -/

/-- A proof method at the strategy level — coarser than ProofMechanism,
    describes the MATHEMATICAL method, not the tactic. -/
inductive ProofMethod where
  | unionBound         -- P(∃ bad h) ≤ Σ P(bad h)
  | concentration      -- iid samples concentrate around expectation
  | symmetrization     -- double sample / ghost sample trick
  | chaining           -- Dudley / generic chaining via covering numbers
  | sauerId            -- growth function bound from VC dimension
  | contrapositive     -- prove ¬A → ¬B then conclude B → A
  | construction       -- build explicit witness (distribution, concept, set)
  | induction          -- mathematical induction (ℕ, Finset, transfinite)
  | bridgeLift         -- transport result across type equivalence
  | measureDecomp      -- decompose measure into parts
  | iidProduct         -- use independence of iid samples
  | exponentialBound   -- (1-ε)^m ≤ exp(-εm)
  | epsilonNet         -- cover space with finitely many balls
  | telescoping        -- telescope sum/product
  | lipschitzTransfer  -- transfer concentration via Lipschitz continuity
  | logSobolev         -- log-Sobolev inequality → concentration
  | varianceDecomp     -- Efron-Stein style variance decomposition
  deriving Repr, BEq, Hashable, Inhabited

/-- A proof strategy as a tree of methods — mirrors CompoundMechanism
    but at the mathematical level, not the tactic level. -/
inductive ProofStrategy where
  | atom (m : ProofMethod)
  | seq (s₁ s₂ : ProofStrategy)
  | branch (label : String) (cases : List ProofStrategy)
  deriving Repr, Inhabited

/-! ## Prior Art Theorem Trace -/

/-- Source library identifier. -/
inductive PriorArtSource where
  | yuanheZ           -- lean-stat-learning-theory (Lean4)
  | googleFormalML    -- formal-ml (Lean3)
  | mathlib           -- Lean4 Mathlib
  | custom (name : String)
  deriving Repr, BEq, Hashable, Inhabited

/-- Lean version tag — critical for import feasibility. -/
inductive LeanVersion where
  | lean3  -- can only use as blueprint (no direct import)
  | lean4  -- can potentially import or adapt
  deriving Repr, BEq, Inhabited

/-- A type mapping from an external library type to our type. -/
structure TypeBridge where
  /-- Their type name (fully qualified) -/
  externalType : String
  /-- Our corresponding type name -/
  internalType : String
  /-- Nature of the mapping -/
  bridgeKind : BridgeKind
  /-- Any conditions required for the bridge -/
  conditions : List String := []
  deriving Repr
where
  inductive BridgeKind where
    | isomorphic       -- exact 1-1 correspondence
    | embedding        -- ours embeds into theirs (or vice versa)
    | specialization   -- theirs is more general; ours is a special case
    | generalization   -- ours is more general; theirs is a special case
    | analogy          -- structurally similar but not formally equivalent
    | incompatible     -- cannot bridge (record WHY)
    deriving Repr, BEq

/-- A single theorem from an external library, captured as a trace. -/
structure PriorArtTheorem where
  /-- Human-readable name -/
  name : String
  /-- Source library -/
  source : PriorArtSource
  /-- Lean version -/
  version : LeanVersion
  /-- Informal statement (captures content across versions) -/
  statement : String
  /-- Proof strategy decomposition -/
  strategy : ProofStrategy
  /-- Type bridges needed to connect to our library -/
  typeBridges : List TypeBridge := []
  /-- Which of our sorry sites could this help close? -/
  targetSorrys : List String := []
  /-- Estimated adaptation difficulty (0 = trivial, 10 = requires new infrastructure) -/
  adaptationDifficulty : Nat := 5
  /-- Dependencies within the same source library -/
  dependencies : List String := []
  deriving Repr

/-! ## Library-Level Traces -/

/-- A complete library trace: all theorems + global metadata. -/
structure LibraryTrace where
  source : PriorArtSource
  version : LeanVersion
  totalLines : Nat
  totalSorrys : Nat
  theorems : Array PriorArtTheorem
  /-- Global type bridges that apply to the entire library -/
  globalBridges : Array TypeBridge := #[]
  /-- What the library is MISSING that we need -/
  gaps : Array String := #[]
  deriving Repr

/-! ## Concrete Library Traces: Yuanhe Z + Google formal-ml -/

/-- Yuanhe Z's lean-stat-learning-theory — concentration inequality infrastructure. -/
def yuanheZTrace : LibraryTrace where
  source := .yuanheZ
  version := .lean4
  totalLines := 34892
  totalSorrys := 0
  globalBridges := #[
    { externalType := "IsSubGaussianProcess"
      internalType := "-- (no direct analog)"
      bridgeKind := .generalization
      conditions := ["would need SubGaussianProcess structure in our library"] },
    { externalType := "coveringNumber"
      internalType := "-- (no direct analog)"
      bridgeKind := .generalization
      conditions := ["metric entropy infrastructure not in our scope"] },
    { externalType := "MeasureTheory.Measure"
      internalType := "MeasureTheory.Measure"
      bridgeKind := .isomorphic
      conditions := ["same Mathlib type — direct reuse"] }
  ]
  gaps := #[
    "NO PAC learning definitions or theorems",
    "NO VC dimension",
    "NO Sauer-Shelah lemma",
    "NO sample complexity",
    "NO Hoeffding inequality (uses sub-Gaussian tail bounds instead)",
    "NO ERM generalization (only least-squares specific bounds)"
  ]
  theorems := #[
    { name := "efronStein"
      source := .yuanheZ
      version := .lean4
      statement := "Var(f(X₁,...,Xₙ)) ≤ Σᵢ E[(f - Eⁱf)²] for independent Xᵢ"
      strategy := .seq (.atom .varianceDecomp) (.atom .iidProduct)
      targetSorrys := []
      adaptationDifficulty := 7
      dependencies := ["condExpExceptCoord", "MemLp"] },
    { name := "subGaussian_tail_bound"
      source := .yuanheZ
      version := .lean4
      statement := "P(|Xₛ - Xₜ| ≥ u) ≤ 2·exp(-u²/(2σ²d(s,t)²))"
      strategy := .seq (.atom .concentration) (.atom .exponentialBound)
      targetSorrys := ["vcdim_finite_imp_pac"]
      adaptationDifficulty := 6
      dependencies := ["IsSubGaussianProcess", "subGaussian_tail_bound_one_sided"] },
    { name := "subGaussian_finite_max_bound"
      source := .yuanheZ
      version := .lean4
      statement := "E[max_{t∈T} Xₜ] ≤ σ·diam(T)·√(2 log|T|)"
      strategy := .seq (.atom .unionBound) (.atom .concentration)
      targetSorrys := ["vcdim_finite_imp_pac"]
      adaptationDifficulty := 5
      dependencies := ["subGaussian_tail_bound"] },
    { name := "dudley_chaining_bound_core"
      source := .yuanheZ
      version := .lean4
      statement := "E[sup_{u ∈ nets_K} (Xᵤ - Xt₀)] ≤ (6√2)σ · dyadicRHS(s,D,K+1)"
      strategy := .seq (.atom .chaining) (.seq (.atom .telescoping) (.atom .concentration))
      targetSorrys := []
      adaptationDifficulty := 9
      dependencies := ["subGaussian_finite_max_bound", "GoodDyadicNets", "metricEntropy"] },
    { name := "master_error_bound"
      source := .yuanheZ
      version := .lean4
      statement := "P(‖f̂-f*‖²ₙ > 16tδ*) ≤ exp(-ntδ*/(2σ²))"
      strategy := .seq (.atom .concentration) (.seq (.atom .chaining) (.atom .lipschitzTransfer))
      targetSorrys := ["vcdim_finite_imp_pac"]
      adaptationDifficulty := 8
      dependencies := ["bad_event_probability_bound", "dudley_empiricalProcess"] },
    { name := "gaussian_lipschitz_concentration"
      source := .yuanheZ
      version := .lean4
      statement := "L-Lipschitz f on Gaussian ⟹ sub-Gaussian with parameter L"
      strategy := .seq (.atom .logSobolev) (.atom .lipschitzTransfer)
      targetSorrys := []
      adaptationDifficulty := 8
      dependencies := ["TensorizedGLSI", "LipschitzMollification"] }
  ]

/-- Google's formal-ml — PAC learning theory (Lean3, blueprint only). -/
def googleFormalMLTrace : LibraryTrace where
  source := .googleFormalML
  version := .lean3
  totalLines := 36221
  totalSorrys := 0
  globalBridges := #[
    { externalType := "PAC_problem"
      internalType := "PACLearnable"
      bridgeKind := .analogy
      conditions := ["Lean3 structure vs Lean4 Prop; quantifier order differs",
                      "Their PAC uses finite hypothesis space; ours uses concept class"] },
    { externalType := "VCD (enat)"
      internalType := "VCDim (WithTop ℕ)"
      bridgeKind := .isomorphic
      conditions := ["enat ≅ WithTop ℕ; shatters definition equivalent via B₃ bridge"] },
    { externalType := "shatters (Lean3)"
      internalType := "Shatters (ours) / Finset.Shatters (Mathlib)"
      bridgeKind := .isomorphic
      conditions := ["restrict_set C S ↔ our shattering; already bridged via B₃"] },
    { externalType := "nnreal.exp"
      internalType := "Real.exp / ENNReal.ofReal"
      bridgeKind := .specialization
      conditions := ["Their bounds use nnreal; ours use ENNReal.ofReal for measure"] }
  ]
  gaps := #[
    "Lean3 — cannot directly import; must translate proof strategies",
    "NO Rademacher complexity",
    "NO Littlestone dimension / online learning",
    "NO Gold-style inductive inference",
    "NO mind change complexity",
    "NO ordinal complexity measures"
  ]
  theorems := #[
    { name := "pac_bound"
      source := .googleFormalML
      version := .lean3
      statement := "1 - |H|·exp(-ε·m) ≤ Pr[all consistent hypotheses have error ≤ ε]"
      strategy := .seq
        (.atom .iidProduct)
        (.seq (.atom .exponentialBound) (.atom .unionBound))
      typeBridges := [
        { externalType := "approximately_correct_event"
          internalType := "PACLearnable success event"
          bridgeKind := .analogy }
      ]
      targetSorrys := ["vcdim_finite_imp_pac", "occam_algorithm"]
      adaptationDifficulty := 4
      dependencies := ["exp_bound2", "fake_hypothesis"] },
    { name := "pac_finite_bound"
      source := .googleFormalML
      version := .lean3
      statement := "For finite |H|, consistent ERM achieves PAC with δ = |H|·exp(-ε·m)"
      strategy := .seq
        (.atom .construction)
        (.seq (.atom .iidProduct) (.seq (.atom .exponentialBound) (.atom .unionBound)))
      targetSorrys := ["vcdim_finite_imp_pac", "occam_algorithm"]
      adaptationDifficulty := 5
      dependencies := ["pac_bound", "consistent_algorithm"] },
    { name := "sauer_shelah (restrict_set_le_phi)"
      source := .googleFormalML
      version := .lean3
      statement := "|{c ∩ S : c ∈ C}| ≤ Φ(VCD(C), |S|) where Φ = growth function"
      strategy := .seq (.atom .induction) (.atom .sauerId)
      typeBridges := [
        { externalType := "restrict_set"
          internalType := "GrowthFunction"
          bridgeKind := .isomorphic }
      ]
      targetSorrys := ["sauer_shelah_quantitative"]
      adaptationDifficulty := 3
      dependencies := ["VCD", "phi_sum"] },
    { name := "VCD definition + shatters"
      source := .googleFormalML
      version := .lean3
      statement := "VCD(C) = Sup{|S| : C shatters S} where shatters = restrict_set = powerset"
      strategy := .atom .bridgeLift
      typeBridges := [
        { externalType := "VCD (enat)"
          internalType := "VCDim (WithTop ℕ)"
          bridgeKind := .isomorphic }
      ]
      targetSorrys := []
      adaptationDifficulty := 1
      dependencies := [] },
    { name := "nnreal_exp_bound2"
      source := .googleFormalML
      version := .lean3
      statement := "(1-x)^k ≤ exp(-x·k) for x : nnreal"
      strategy := .seq (.atom .exponentialBound) (.atom .induction)
      targetSorrys := ["vcdim_finite_imp_pac", "occam_algorithm"]
      adaptationDifficulty := 3
      dependencies := ["exp_bound3"] },
    { name := "vc_pac_bounds"
      source := .googleFormalML
      version := .lean3
      statement := "VCD(C) < ∞ ⟹ PAC-learnable via growth function + uniform convergence"
      strategy := .seq
        (.atom .sauerId)
        (.seq (.atom .exponentialBound) (.seq (.atom .unionBound) (.atom .construction)))
      targetSorrys := ["vc_characterization", "vcdim_finite_imp_pac"]
      adaptationDifficulty := 6
      dependencies := ["restrict_set_le_phi", "pac_bound", "VCD"] }
  ]

/-! ## Trace Queries: What can prior-art tell us about a sorry? -/

/-- Find all prior-art theorems that target a specific sorry. -/
def findRelevantTheorems (sorryName : String) (libs : List LibraryTrace) :
    List PriorArtTheorem :=
  libs.foldl (fun acc lib =>
    acc ++ (lib.theorems.toList.filter fun t => t.targetSorrys.contains sorryName)) []

/-- Extract the proof strategy chain for closing a sorry. -/
def extractStrategyChain (sorryName : String) (libs : List LibraryTrace) :
    List (String × ProofStrategy) :=
  let relevant := findRelevantTheorems sorryName libs
  relevant.map fun t => (t.name, t.strategy)

/-- Compute adaptation cost for a sorry: minimum difficulty across all relevant theorems. -/
def minAdaptationCost (sorryName : String) (libs : List LibraryTrace) : Nat :=
  let relevant := findRelevantTheorems sorryName libs
  match relevant.map (·.adaptationDifficulty) |>.minimum? with
  | some n => n
  | none => 10  -- no prior art → maximum difficulty

/-- Get all type bridges needed for a sorry from prior art. -/
def requiredBridges (sorryName : String) (libs : List LibraryTrace) :
    List TypeBridge :=
  let relevant := findRelevantTheorems sorryName libs
  relevant.foldl (fun acc t => acc ++ t.typeBridges) []

/-! ## World Model State: What the MetaKernel knows about external knowledge -/

/-- The MetaKernel's world model: everything it knows about the proof landscape,
    including both internal state (KernelState) and external knowledge (prior-art). -/
structure WorldModelState where
  /-- Prior-art library traces -/
  libraries : List LibraryTrace := [yuanheZTrace, googleFormalMLTrace]
  /-- Sorry → best known proof strategy from prior art -/
  strategyCache : Std.HashMap String ProofStrategy := {}
  /-- Sorry → required type bridges -/
  bridgeCache : Std.HashMap String (List TypeBridge) := {}
  /-- UU→UK transitions discovered: things we didn't know we didn't know, now identified -/
  ukDiscoveries : Array String := #[]
  /-- KU→KK transitions: sorrys we've closed using prior art -/
  kkTransitions : Array String := #[]
  deriving Inhabited

/-- Initialize the world model by scanning all prior-art for each known sorry. -/
def WorldModelState.init (sorrySites : List String) : WorldModelState :=
  let libs := [yuanheZTrace, googleFormalMLTrace]
  let mut cache : Std.HashMap String ProofStrategy := {}
  let mut bridges : Std.HashMap String (List TypeBridge) := {}
  for sorry in sorrySites do
    let chains := extractStrategyChain sorry libs
    match chains.head? with
    | some (_, strategy) => cache := cache.insert sorry strategy
    | none => ()
    let bs := requiredBridges sorry libs
    if !bs.isEmpty then
      bridges := bridges.insert sorry bs
  { libraries := libs
    strategyCache := cache
    bridgeCache := bridges }

end MetaKernel.WorldModel
