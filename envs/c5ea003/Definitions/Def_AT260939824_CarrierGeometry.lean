-- Prove2me | Definitions.Def_AT260939824_CarrierGeometry
-- name    : AT260939824_CarrierGeometry
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T02:46:59.626445+00:00
-- url     : https://prove2.me/theorems/6758c421-de6f-45fb-af32-6b4ead302009
-- title:
--   Finite simplicial probability realizations of interval carriers
-- statement:
--   Fix a base $m$, height $K$, and integer interval $[A,B]$. The carrier vertex type consists of the finite set of vertices in that interval and height range. A point of its realization is a probability distribution supported on one permitted finite face:
--
--   $$ \mathcal C_m^K([A,B])=\bigcup_{s\text{ permitted}}\Delta_s. $$
--
--   Each support face is closed, and the realization is a closed compact subspace of the finite probability simplex. The inherited mass-coordinate metric and Dirac vertex points make it a concrete metric space for subsequent homotopies.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (2026), Section(s) 4; https://arxiv.org/abs/2609.39824v1. This item is auxiliary infrastructure of the accompanying formalization, not a claim that each implementation definition is separately numbered in the paper. Original Lean module AbelianTargets/CarrierGeometry.lean, selected declaration lines 25-34, 36-54, 56-67, 73, 75-77, 79-81, 83-87, 89-90, 92-93, 95-96, 98-99, 101-113, 115-116, 118-123; SHA-256 6a4ee447c955848ca01afc3b9cb5cdde3da3e0384718587aac61df96e64d0c17. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_CarrierCellRealization
import Definitions.Def_AT260939824_CarrierTriangulation
import Definitions.Def_AT260939824_CompressedWords
import Definitions.Def_AT260939824_DigitPathRealization
import Definitions.Def_AT260939824_FixedSlotInterpolation
import Definitions.Def_AT260939824_IntervalCarriers
import Definitions.Def_AT260939824_Probability
import Definitions.Def_AT260939824_RelativePathContraction
import Definitions.Def_AT260939824_Rounding
import Definitions.Def_AT260939824_SupportGeometry
import Definitions.Def_AT260939824_SupportModel
import Init
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Algebra.Group.Conj
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Int.Interval
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Constructions
import Mathlib.Topology.Homotopy.Path
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.Path
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Separation.Profinite
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.UnitInterval

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

/-!
# The actual finite barycentric interval carrier

The carrier is the union of the probability-simplex faces specified by
the finite fan triangulation. Its vertices and simplex charts are actual
points and continuous maps. No contraction is included as an assumption.
-/

namespace AbelianTargets

open scoped BigOperators NNReal

noncomputable section

namespace Probability

variable {V : Type*} [Fintype V]

theorem supportedOn_iff_zero {p : Probability V} {A : Set V} :
    p.SupportedOn A ↔ ∀ v, v ∉ A → p.mass v = 0 := by
  constructor
  · intro h v hv
    by_contra hne
    exact hv (h v (lt_of_le_of_ne (p.nonneg v) (Ne.symm hne)))
  · intro h v hv
    by_contra hnot
    rw [h v hnot] at hv
    exact (lt_irrefl _ hv)

theorem isClosed_supportedOn (A : Set V) : IsClosed {p : Probability V | p.SupportedOn A} := by
  have he : {p : Probability V | p.SupportedOn A} =
      ⋂ v : V, {p | v ∈ A ∨ p.mass v = 0} := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_iInter, supportedOn_iff_zero]
    constructor
    · intro h v
      by_cases hv : v ∈ A
      · exact Or.inl hv
      · exact Or.inr (h v hv)
    · intro h v hv
      exact (h v).resolve_left hv
  rw [he]
  apply isClosed_iInter
  intro v
  by_cases hv : v ∈ A
  · simp [hv]
  · simpa only [hv, false_or] using
      isClosed_eq (continuous_mass_apply v) continuous_const

theorem dist_le_one (p q : Probability V) : dist p q ≤ 1 := by
  change dist p.mass q.mass ≤ 1
  apply (dist_pi_le_iff (by norm_num : (0 : ℝ) ≤ 1)).2
  intro v
  rw [Real.dist_eq, abs_le]
  constructor
  · have hp := p.nonneg v
    have hq := q.mass_le_one v
    linarith
  · have hp := p.mass_le_one v
    have hq := q.nonneg v
    linarith

end Probability

namespace IntervalCarriers

abbrev CarrierVertex (K : ℕ) (A B : ℤ) := {v : Vertex // v ∈ carrierVertices K A B}

instance (K : ℕ) (A B : ℤ) : Fintype (CarrierVertex K A B) := by
  classical
  exact Fintype.ofFinset (carrierVertices K A B) (by simp)

def simplexFaces (m K : ℕ) (A B : ℤ) : Finset (Finset (CarrierVertex K A B)) := by
  classical
  exact Finset.univ.powerset.filter (fun s => CarrierFace m K A B (s.image Subtype.val))

theorem mem_simplexFaces {m K : ℕ} {A B : ℤ} (s : Finset (CarrierVertex K A B)) :
    s ∈ simplexFaces m K A B ↔ CarrierFace m K A B (s.image Subtype.val) := by
  classical
  simp only [simplexFaces, Finset.mem_filter, Finset.mem_powerset]
  exact and_iff_right (Finset.subset_univ s)

def InRealization (m K : ℕ) (A B : ℤ) (p : Probability (CarrierVertex K A B)) : Prop :=
  ∃ s ∈ simplexFaces m K A B, p.SupportedOn (s : Set _)

def Realization (m K : ℕ) (A B : ℤ) :=
  {p : Probability (CarrierVertex K A B) // InRealization m K A B p}

instance (m K : ℕ) (A B : ℤ) : TopologicalSpace (Realization m K A B) :=
  inferInstanceAs (TopologicalSpace (Subtype _))

instance (m K : ℕ) (A B : ℤ) : MetricSpace (Realization m K A B) :=
  inferInstanceAs (MetricSpace (Subtype _))

theorem isClosed_inRealization (m K : ℕ) (A B : ℤ) :
    IsClosed {p : Probability (CarrierVertex K A B) | InRealization m K A B p} := by
  have he : {p : Probability (CarrierVertex K A B) | InRealization m K A B p} =
      ⋃ s ∈ simplexFaces m K A B, {p | p.SupportedOn (s : Set _)} := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, InRealization]
    constructor
    · rintro ⟨s,hs,hp⟩
      exact ⟨s,hs,hp⟩
    · rintro ⟨s,hs,hp⟩
      exact ⟨s,hs,hp⟩
  rw [he]
  exact isClosed_biUnion_finset (fun s _ => Probability.isClosed_supportedOn (V := CarrierVertex K A B) (s : Set _))

instance (m K : ℕ) (A B : ℤ) : CompactSpace (Realization m K A B) :=
  isCompact_iff_compactSpace.mp (isClosed_inRealization m K A B).isCompact

def point {m K : ℕ} {A B : ℤ} (v : CarrierVertex K A B) : Realization m K A B := by
  refine ⟨Probability.dirac v, {v}, ?_, Probability.supportedOn_dirac v (by simp)⟩
  apply (mem_simplexFaces {v}).mpr
  classical
  simp only [Finset.image_singleton]
  exact Or.inl ⟨v.1,v.2,Finset.Subset.refl _⟩









end IntervalCarriers

end

end AbelianTargets


