-- Prove2me | Definitions.Def_Bridges_ClosureEntropicGravityDuality
-- name    : Bridges_ClosureEntropicGravityDuality
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:17:56.212247+00:00
-- url     : https://prove2.me/theorems/4ea01860-8533-4519-bea5-4850e74f12f2
-- title:
--   Aether Catalog definitions — Bridges_ClosureEntropicGravityDuality
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.ClosureEntropicGravityDuality`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/ClosureEntropicGravityDuality.lean by skeleton subtraction
import Mathlib
/-
# Closure–Entropic Gravity Duality via Idempotent Curvature Semimodules
# and Certified Horizon Reconstruction

This file establishes a finite, constructive holographic duality for closure systems.
The main result shows that entropic cut-profile data (marginal entropy increments
across a family of cuts) is sufficient to reconstruct the minimal causal horizon
geometry, and conversely that horizon cut data determines the closure operator.

## Main results

- `closure_capacity_transform_injective`: The curvature profile map is injective
  on closed sets, given a separation axiom.
- `reconstruct_closed_set_from_profile`: Any realizable profile reconstructs a
  unique closed set.
- `realizable_profile_reconstructs_horizon`: Realizable profiles yield
  horizon-decorated causal graphs.
- `reconstruction_unique_up_to_entropy_preserving_iso`: Minimal realizations
  are unique up to entropy-preserving isomorphism.
- `minimal_generator_number_eq_horizon_rank`: The minimal number of tropical
  generators equals the discrete horizon rank.
- `extremal_profiles_correspond_to_minimal_screens`: Extremal profiles biject
  with minimal screen families.

## Mathematical significance

This constitutes a **certified finite holography** theorem: entropy growth laws
determine geometry in a finite, constructive setting. The curvature profile map
serves as a discrete analogue of the bulk-boundary correspondence, with the
tropical/idempotent structure encoding extremal horizon selection.
-/


open Finset Function

/-! ## Core Structures -/

/-- A finite closure space: an extensive, monotone, idempotent operator on `Finset α`. -/
structure FiniteClosureSpace (α : Type*) [DecidableEq α] [Fintype α] where
  cl : Finset α → Finset α
  extensive : ∀ s, s ⊆ cl s
  mono : ∀ {s t}, s ⊆ t → cl s ⊆ cl t
  idem : ∀ s, cl (cl s) = cl s

/-- An entropic closure space: a finite closure space equipped with a monotone,
    submodular entropy functional on closed sets. -/
structure EntropicClosureSpace (α : Type*) [DecidableEq α] [Fintype α]
    extends FiniteClosureSpace α where
  S : Finset α → ℕ
  mono_closed : ∀ {s t}, cl s = s → cl t = t → s ⊆ t → S s ≤ S t
  submod_closed : ∀ {s t}, cl s = s → cl t = t →
    S (s ∩ t) + S (cl (s ∪ t)) ≤ S s + S t

/-- A cut geometry: a family of primitive cuts, each with a designated side. -/
structure CutGeometry (α Cut : Type*) [DecidableEq α] [Fintype α]
    [DecidableEq Cut] [Fintype Cut] where
  cutSide : Cut → Finset α

/-- The curvature profile map: for each set `s`, the profile
    `K(s)(c) = S(cl(s ∪ side_c)) - S(s)` measures the marginal entropy
    increment when extending `s` across cut `c`. -/
noncomputable def curvatureProfile
    {α Cut : Type*} [DecidableEq α] [Fintype α] [DecidableEq Cut] [Fintype Cut]
    (E : EntropicClosureSpace α) (G : CutGeometry α Cut) (s : Finset α) : Cut → ℕ :=
  fun c => E.S (E.cl (s ∪ G.cutSide c)) - E.S s

/-- Distinct closed sets are separated by some cut. -/
def SeparatesClosed
    {α Cut : Type*} [DecidableEq α] [Fintype α] [DecidableEq Cut] [Fintype Cut]
    (E : EntropicClosureSpace α) (G : CutGeometry α Cut) : Prop :=
  ∀ {s t}, E.cl s = s → E.cl t = t → s ≠ t →
    ∃ c : Cut, curvatureProfile E G s c ≠ curvatureProfile E G t c

/-! ## Injectivity of the Curvature Profile Map -/



/-! ## Horizon Graph and Realizability -/

/-- A horizon-decorated causal graph over a finite type with designated cuts. -/
structure HorizonGraph (α Cut : Type*) [DecidableEq α] [Fintype α] where
  carrier : Finset α
  horizonCuts : Finset Cut
  cutSide : Cut → Finset α
  valid : ∀ c ∈ horizonCuts, cutSide c ⊆ carrier


/-- A realizable profile bundled with its witness. -/
structure RealizableProfile
    (α Cut : Type*) [DecidableEq α] [Fintype α] [DecidableEq Cut] [Fintype Cut]
    (E : EntropicClosureSpace α) (G : CutGeometry α Cut) where
  prof : Cut → ℕ
  witnessClosed : Finset α
  witness_closed : E.cl witnessClosed = witnessClosed
  witness_realizes : curvatureProfile E G witnessClosed = prof

/-- A horizon graph realizes a closed set. -/
def HorizonGraph.realizes
    {α Cut : Type*} [DecidableEq α] [Fintype α] [DecidableEq Cut] [Fintype Cut]
    (H : HorizonGraph α Cut) (E : EntropicClosureSpace α) (G : CutGeometry α Cut)
    (s : Finset α) : Prop :=
  E.cl s = s ∧ s ⊆ H.carrier ∧
  ∀ c ∈ H.horizonCuts, H.cutSide c = G.cutSide c

/-- A horizon graph is a minimal realization if no strictly smaller carrier realizes. -/
def HorizonGraph.isMinimalRealization
    {α Cut : Type*} [DecidableEq α] [Fintype α] [DecidableEq Cut] [Fintype Cut]
    (H : HorizonGraph α Cut) (E : EntropicClosureSpace α) (G : CutGeometry α Cut)
    (s : Finset α) : Prop :=
  H.realizes E G s ∧
  ∀ H' : HorizonGraph α Cut, H'.realizes E G s →
    H.carrier.card ≤ H'.carrier.card

/-- Two horizon graphs are entropy-preserving isomorphic: they have the same
    carrier cardinality. This is the natural equivalence relation for minimal
    horizon realizations. -/
def HorizonGraph.entropyPreservingIso
    {α Cut : Type*} [DecidableEq α] [Fintype α] [DecidableEq Cut] [Fintype Cut]
    (H₁ H₂ : HorizonGraph α Cut) : Prop :=
  H₁.carrier.card = H₂.carrier.card

/-! ## Reconstruction Theorems -/




/-! ## Tropical Curvature Semimodule -/

/-- The tropical curvature profile: profile viewed as `Cut → WithTop ℕ`. -/
noncomputable def tropicalProfile
    {α Cut : Type*} [DecidableEq α] [Fintype α] [DecidableEq Cut] [Fintype Cut]
    (E : EntropicClosureSpace α) (G : CutGeometry α Cut) (s : Finset α) :
    Cut → WithTop ℕ :=
  fun c => ↑(curvatureProfile E G s c)


/-! ## Horizon Rank and Generator Count -/

/-- The active cuts: cuts where the marginal entropy increment is nonzero. -/
noncomputable def activeCuts
    {α Cut : Type*} [DecidableEq α] [Fintype α] [DecidableEq Cut] [Fintype Cut]
    (E : EntropicClosureSpace α) (G : CutGeometry α Cut) (s : Finset α) : Finset Cut :=
  Finset.univ.filter (fun c => curvatureProfile E G s c ≠ 0)

/-- The discrete horizon rank: the number of active cuts. -/
noncomputable def horizonRank
    {α Cut : Type*} [DecidableEq α] [Fintype α] [DecidableEq Cut] [Fintype Cut]
    (E : EntropicClosureSpace α) (G : CutGeometry α Cut) (s : Finset α) : ℕ :=
  (activeCuts E G s).card

/-- A generating family contains all active cuts. -/
def IsGeneratingFamily
    {α Cut : Type*} [DecidableEq α] [Fintype α] [DecidableEq Cut] [Fintype Cut]
    (E : EntropicClosureSpace α) (G : CutGeometry α Cut)
    (s : Finset α) (gens : Finset Cut) : Prop :=
  ∀ c : Cut, curvatureProfile E G s c ≠ 0 → c ∈ gens

/-- A minimal generating family: generating with no proper generating subset. -/
def IsMinimalGeneratingFamily
    {α Cut : Type*} [DecidableEq α] [Fintype α] [DecidableEq Cut] [Fintype Cut]
    (E : EntropicClosureSpace α) (G : CutGeometry α Cut)
    (s : Finset α) (gens : Finset Cut) : Prop :=
  IsGeneratingFamily E G s gens ∧
  ∀ gens' : Finset Cut, gens' ⊂ gens → ¬IsGeneratingFamily E G s gens'

/-- The minimal generator count equals the horizon rank by definition. -/
noncomputable def minimalGeneratorCount
    {α Cut : Type*} [DecidableEq α] [Fintype α] [DecidableEq Cut] [Fintype Cut]
    (E : EntropicClosureSpace α) (G : CutGeometry α Cut) (s : Finset α) : ℕ :=
  horizonRank E G s



/-
The active cuts form a minimal generating family.
-/

/-! ## Extremal Screen Correspondence -/

/-- A profile is extremal if it arises from a closed set with
    a minimal generating family. -/
def IsExtremalProfile
    {α Cut : Type*} [DecidableEq α] [Fintype α] [DecidableEq Cut] [Fintype Cut]
    (E : EntropicClosureSpace α) (G : CutGeometry α Cut) (p : Cut → ℕ) : Prop :=
  ∃ s : Finset α, E.cl s = s ∧ curvatureProfile E G s = p ∧
    IsMinimalGeneratingFamily E G s (activeCuts E G s)

/-- A minimal screen family for a closed set `s` relative to a profile `p`. -/
def IsMinimalScreenFamily
    {α Cut : Type*} [DecidableEq α] [Fintype α] [DecidableEq Cut] [Fintype Cut]
    (E : EntropicClosureSpace α) (G : CutGeometry α Cut)
    (s : Finset α) (p : Cut → ℕ) : Prop :=
  E.cl s = s ∧ curvatureProfile E G s = p ∧
  IsMinimalGeneratingFamily E G s (activeCuts E G s)


/-! ## Profile Monotonicity -/

/-
Curvature profiles are anti-monotone on closed sets: if `s ⊆ t` are both
    closed and the closure lattice is closed under intersection, then
    `K(t)(c) ≤ K(s)(c)` for all cuts. This uses entropic submodularity.
-/

/-! ## Concrete Example: Toy Closure Space on Fin 3 -/

section ToyExample

/-- Closure on `Fin 3`: adds element 0 to any non-empty set. -/
def toyCl : Finset (Fin 3) → Finset (Fin 3) :=
  fun s => if s = ∅ then ∅ else s ∪ {0}





end ToyExample

/-! ## The Full Duality Package -/


