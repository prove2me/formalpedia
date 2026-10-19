-- Prove2me | Definitions.Def_AT260939824_FanStageTransitions
-- name    : AT260939824_FanStageTransitions
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T03:11:53.819109+00:00
-- url     : https://prove2.me/theorems/bfc46e15-735f-492e-87aa-30200825e82a
-- title:
--   Successive carrier fan retractions
-- statement:
--   For a finite interval carrier with base $m\ge1$, height $K+1$, and integer horizontal bounds $A,B$, the terminal state of the top collapse lies in the initial polygon-fan complex. Each subsequent fan collapse has terminal support in the preceding fan complex. The bundle constructs these typed retractions and proves downward closure and positive-support membership, allowing the individual stages to compose literally.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Sections 2-7; https://arxiv.org/html/2609.39824v1. Formalization-specific infrastructure in the import closure of Theorem 1.4 and Proposition 7.1; individual helper assertions are not represented as separately numbered paper theorems. Original Lean module AbelianTargets/FanStageTransitions.lean, selected declaration lines 9-13, 15-18, 20-23, 25-33, 35-48, 50-53, 59-75, 77-80; SHA-256 c79f49b77a3a05f179705afa3e29e15a8b25e62d707929142fcd0c06f85519d6. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_CarrierCellRealization
import Definitions.Def_AT260939824_CarrierGeometry
import Definitions.Def_AT260939824_CarrierTriangulation
import Definitions.Def_AT260939824_CompressedWords
import Definitions.Def_AT260939824_DigitPathRealization
import Definitions.Def_AT260939824_FixedSlotInterpolation
import Definitions.Def_AT260939824_IntervalCarriers
import Definitions.Def_AT260939824_LowerCarrierCollapse
import Definitions.Def_AT260939824_ParallelCollapse
import Definitions.Def_AT260939824_Probability
import Definitions.Def_AT260939824_RelativePathContraction
import Definitions.Def_AT260939824_Rounding
import Definitions.Def_AT260939824_SimplexMetricGluing
import Definitions.Def_AT260939824_SimplicialSupport
import Definitions.Def_AT260939824_SupportGeometry
import Definitions.Def_AT260939824_SupportModel
import Definitions.Def_AT260939824_TriangleCollapse
import Definitions.Def_AT260939824_UpperCarrierCollapse
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
import Mathlib.Tactic.FieldSimp
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

namespace AbelianTargets.IntervalCarriers
noncomputable section
attribute [local instance] Classical.propDecidable

theorem FanAdmissible.downward {m K t : ℕ} {A B : ℤ} {s u : Finset Vertex}
    (hs : FanAdmissible m K A B t s) (hu : u ⊆ s) : FanAdmissible m K A B t u := by
  constructor
  · intro c h; exact hs.1 c ⟨hu h.1,hu h.2⟩
  · intro c k hk hkm h; exact hs.2 c k hk hkm ⟨hu h.1,hu h.2⟩

theorem fanFaces_downward {m K t : ℕ} {A B : ℤ} {s u : Finset (CarrierVertex (K+1) A B)}
    (hs : s ∈ fanFaces m K A B t) (hu : u ⊆ s) : u ∈ fanFaces m K A B t := by
  obtain ⟨hs,ha⟩ := (mem_fanFaces s).mp hs
  exact (mem_fanFaces u).mpr ⟨simplexFaces_downward hs hu,ha.downward (Finset.image_subset_image hu)⟩

theorem positiveSupport_mem_fan {m K t : ℕ} {A B : ℤ}
    (p : SimplicialCarrier (fanFaces m K A B t)) : p.1.positiveSupport ∈ fanFaces m K A B t := by
  obtain ⟨s,hs,hp⟩ := p.2
  exact fanFaces_downward hs (p.1.positiveSupport_subset hp)

theorem mem_positiveSupport_image {K : ℕ} {A B : ℤ} (p : Probability (CarrierVertex K A B))
    (v : CarrierVertex K A B) : v.1 ∈ p.positiveSupport.image Subtype.val ↔ 0 < p.mass v := by
  constructor
  · intro h
    obtain ⟨w,hw,he⟩ := Finset.mem_image.mp h
    have hv : w = v := Subtype.ext he
    simpa only [hv] using (Probability.mem_positiveSupport p w).mp hw
  · intro h
    exact Finset.mem_image.mpr ⟨v,(Probability.mem_positiveSupport p v).mpr h,rfl⟩

theorem collapseTop_terminal {m K : ℕ} {A B : ℤ} (hm : 1 ≤ m) (p : Realization m (K+1) A B) :
    (collapseTop hm p 1).1.positiveSupport ∈ fanFaces m K A B m := by
  apply (mem_fanFaces _).mpr
  refine ⟨positiveSupport_mem _,?_,?_⟩
  · intro c h
    have ha : 0 < (collapseTop hm p 1).1.mass (topTriangle hm c).a :=
      (mem_positiveSupport_image _ (topTriangle hm c).a).mp h.1
    have hb : 0 < (collapseTop hm p 1).1.mass (topTriangle hm c).b :=
      (mem_positiveSupport_image _ (topTriangle hm c).b).mp h.2
    rcases collapseTop_removes hm p c with hz | hz
    · rw [hz] at ha; exact lt_irrefl _ ha
    · rw [hz] at hb; exact lt_irrefl _ hb
  · intro c k hk hkm
    omega

def initialFan {m K : ℕ} {A B : ℤ} (hm : 1 ≤ m) (p : Realization m (K+1) A B) :
    SimplicialCarrier (fanFaces m K A B m) :=
  ⟨(collapseTop hm p 1).1,_,collapseTop_terminal hm p,
    Probability.supportedOn_positiveSupport _⟩



theorem collapseFan_terminal {m K n : ℕ} {A B : ℤ} (hm : 1 ≤ m) (hn : n < m)
    (p : SimplicialCarrier (fanFaces m K A B (n+1))) :
    (collapseFan hm hn p 1).1.positiveSupport ∈ fanFaces m K A B n := by
  obtain ⟨hs,hallowed⟩ := (mem_fanFaces _).mp (positiveSupport_mem_fan (collapseFan hm hn p 1))
  apply (mem_fanFaces _).mpr
  refine ⟨hs,hallowed.1,?_⟩
  intro c k hk hkm h
  by_cases hkn : k = n
  · subst k
    have ha : 0 < (collapseFan hm hn p 1).1.mass (fanTriangle hm hn c).a :=
      (mem_positiveSupport_image _ (fanTriangle hm hn c).a).mp h.1
    have hb : 0 < (collapseFan hm hn p 1).1.mass (fanTriangle hm hn c).b :=
      (mem_positiveSupport_image _ (fanTriangle hm hn c).b).mp h.2
    rcases collapseFan_removes hm hn p c with hz | hz
    · rw [hz] at ha; exact lt_irrefl _ ha
    · rw [hz] at hb; exact lt_irrefl _ hb
  · exact hallowed.2 c k (by omega) hkm h

def fanRetraction {m K n : ℕ} {A B : ℤ} (hm : 1 ≤ m) (hn : n < m)
    (p : SimplicialCarrier (fanFaces m K A B (n+1))) : SimplicialCarrier (fanFaces m K A B n) :=
  ⟨(collapseFan hm hn p 1).1,_,collapseFan_terminal hm hn p,
    Probability.supportedOn_positiveSupport _⟩



end
end AbelianTargets.IntervalCarriers


