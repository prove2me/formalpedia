-- Prove2me | Definitions.Def_AT260939824_GeneralCarrierHeightRestriction
-- name    : AT260939824_GeneralCarrierHeightRestriction
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T03:17:30.101686+00:00
-- url     : https://prove2.me/theorems/f919470f-470a-4c9a-921b-2373faa69ece
-- title:
--   Restriction to a lower carrier height
-- statement:
--   For base $m\ge1$, integer bounds $A,B$, and heights $K\le T$, a carrier face at height $T$ whose vertices all lie at height at most $K$ is already a face of the lower carrier. A probability realization with that positive-support bound can therefore be transferred to height $K$. The construction uses an explicit vertex-floor map and preserves the actual face witness.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Sections 2-7; https://arxiv.org/html/2609.39824v1. Formalization-specific infrastructure in the import closure of Theorem 1.4 and Proposition 7.1; individual helper assertions are not represented as separately numbered paper theorems. Original Lean module AbelianTargets/GeneralCarrierHeightRestriction.lean, selected declaration lines 9-22, 24-26, 28-53, 55-65; SHA-256 93b1304beccc1b9ff51418dfcd263e7379452780555bc65592c270bcec621c92. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_CarrierCellRealization
import Definitions.Def_AT260939824_CarrierGeometry
import Definitions.Def_AT260939824_CarrierHeightCut
import Definitions.Def_AT260939824_CarrierNesting
import Definitions.Def_AT260939824_CarrierTriangulation
import Definitions.Def_AT260939824_CompressedWords
import Definitions.Def_AT260939824_DigitPathRealization
import Definitions.Def_AT260939824_FixedSlotInterpolation
import Definitions.Def_AT260939824_IntervalCarriers
import Definitions.Def_AT260939824_Probability
import Definitions.Def_AT260939824_ProbabilityMap
import Definitions.Def_AT260939824_ProbabilityPushGeometry
import Definitions.Def_AT260939824_RelativePathContraction
import Definitions.Def_AT260939824_Rounding
import Definitions.Def_AT260939824_SimplicialSupport
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

theorem CarrierFace.of_height_le {m K T : ℕ} {A B : ℤ} (hm : 1 ≤ m)
    (hKT : K ≤ T) {s : Finset Vertex} (hs : CarrierFace m T A B s)
    (hheight : ∀ v ∈ s,v.2 ≤ K) : CarrierFace m K A B s := by
  induction T generalizing K with
  | zero =>
    have he : K=0 := by omega
    subst K
    exact hs
  | succ T ih =>
    by_cases h : K ≤ T
    · exact ih h (hs.lower_of_height hm (fun v hv => (hheight v hv).trans h)) hheight
    · have he : K=T+1 := by omega
      subst K
      exact hs

def vertexFloor {K T : ℕ} {A B : ℤ} (v : CarrierVertex T A B) : CarrierVertex K A B :=
  ⟨(v.1.1,min v.1.2 K),mem_carrierVertices.mpr
    ⟨(mem_carrierVertices.mp v.2).1,(mem_carrierVertices.mp v.2).2.1,min_le_right _ _⟩⟩

/-- Restrict an actual probability realization whose positive support has height at most `K`.
No geometric existence hypothesis is added: the face witness is lowered one layer at a time. -/
def restrictCarrierHeight {m K T : ℕ} {A B : ℤ} (hm : 1 ≤ m) (hKT : K ≤ T)
    (p : Realization m T A B) (hp : ∀ v,0 < p.1.mass v → v.1.2 ≤ K) :
    Realization m K A B := by
  refine ⟨Probability.push (vertexFloor (K := K)) p.1,?_⟩
  let s := p.1.positiveSupport
  have hs : s ∈ simplexFaces m T A B := positiveSupport_mem p
  have hface := ((mem_simplexFaces s).mp hs).of_height_le hm hKT (by
    intro v hv
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv
    exact hp w ((Probability.mem_positiveSupport p.1 w).mp hw))
  refine ⟨s.image (vertexFloor (K := K)),?_,?_⟩
  · apply (mem_simplexFaces _).mpr
    rw [Finset.image_image]
    have he : s.image (fun v => (vertexFloor (K := K) v).1) = s.image Subtype.val := by
      apply Finset.image_congr
      intro v hv
      have hh := hp v ((Probability.mem_positiveSupport p.1 v).mp hv)
      simp only [vertexFloor,min_eq_left hh,Prod.eta]
    change CarrierFace m K A B (s.image (fun v => (vertexFloor (K := K) v).1))
    rw [he]
    exact hface
  · intro w hw
    obtain ⟨v,hv,hvp⟩ := (Probability.push_pos_iff (vertexFloor (K := K)) p.1 w).mp hw
    exact Finset.mem_image.mpr ⟨v,(Probability.mem_positiveSupport p.1 v).mpr hvp,hv⟩

theorem carrierInclude_restrictCarrierHeight {m K T : ℕ} {A B : ℤ}
    (hm : 1 ≤ m) (hKT : K ≤ T) (p : Realization m T A B)
    (hp : ∀ v,0 < p.1.mass v → v.1.2 ≤ K) :
    carrierInclude hKT (restrictCarrierHeight hm hKT p hp)=p := by
  apply Subtype.ext
  change Probability.push (vertexInclude hKT) (Probability.push (vertexFloor (K := K)) p.1)=p.1
  rw [Probability.push_comp]
  apply Probability.push_eq_self
  intro v hv
  apply Subtype.ext
  simp only [Function.comp_def,vertexInclude,vertexFloor,min_eq_left (hp v hv),Prod.eta]



end
end AbelianTargets.IntervalCarriers


