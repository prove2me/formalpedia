-- Prove2me | Definitions.Def_AT260939824_VerticalCarrierCollapse
-- name    : AT260939824_VerticalCarrierCollapse
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T03:13:19.629068+00:00
-- url     : https://prove2.me/theorems/923acb20-644a-4cdb-a93a-70552584d516
-- title:
--   Vertical projection after the terminal fan collapse
-- statement:
--   For carrier vertices $(x,h)$ of height at most $K+1$, define the idempotent floor map $f(x,h)=(x,\min(h,K))$. On probability masses set
--   $$H_{\mathrm{vert}}(\mu,t)=(1-t)\mu+t\,f_*\mu.$$
--   Its tracks are $1$-Lipschitz and its joint Lipschitz constant is bounded by $2+|V_{K+1}[A,B]|$ in the maximum metric. For $m\ge1$, a mass in the terminal fan carrier has any remaining top-height support confined to one vertical pair. Therefore this interpolation stays in the original carrier realization; at time one every positive support vertex has height at most $K$. This supplies the final step of a height-lowering deformation. At time zero the vertical collapse equals the original carrier point.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Sections 2–7, supporting construction for Theorem 1.4 and Proposition 7.1; https://arxiv.org/html/2609.39824v1. Formalization-specific infrastructure in the import closure; individual helper assertions are not represented as separately numbered paper theorems. Original Lean module AbelianTargets/VerticalCarrierCollapse.lean, selected declaration lines 13-16, 18-23, 25-26, 33-39, 41-63, 65-69, 71-90, 92-123, 125-127, 145-147, 149-156; SHA-256 542b576739de5781e375faefe5032a463b21c44488d5eb9a67a20621a1e8fb9e. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_CarrierCellRealization
import Definitions.Def_AT260939824_CarrierGeometry
import Definitions.Def_AT260939824_CarrierTriangulation
import Definitions.Def_AT260939824_CompressedWords
import Definitions.Def_AT260939824_DigitPathRealization
import Definitions.Def_AT260939824_FanStageTransitions
import Definitions.Def_AT260939824_FixedSlotInterpolation
import Definitions.Def_AT260939824_IntervalCarriers
import Definitions.Def_AT260939824_LowerCarrierCollapse
import Definitions.Def_AT260939824_ParallelCollapse
import Definitions.Def_AT260939824_Probability
import Definitions.Def_AT260939824_ProbabilityMap
import Definitions.Def_AT260939824_ProbabilityPushGeometry
import Definitions.Def_AT260939824_RelativePathContraction
import Definitions.Def_AT260939824_Rounding
import Definitions.Def_AT260939824_SimplexMetricGluing
import Definitions.Def_AT260939824_SimplicialSupport
import Definitions.Def_AT260939824_SupportGeometry
import Definitions.Def_AT260939824_SupportModel
import Definitions.Def_AT260939824_TriangleCollapse
import Definitions.Def_AT260939824_UpperCarrierCollapse
import Definitions.Def_AT260939824_VerticalCarrierFaces
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

/-! The final speed-one vertical collapse of a literal carrier height layer. -/

namespace AbelianTargets.IntervalCarriers
open scoped NNReal
noncomputable section
attribute [local instance] Classical.propDecidable

def floorVertex {K : ℕ} {A B : ℤ} (v : CarrierVertex (K+1) A B) : CarrierVertex (K+1) A B :=
  ⟨(v.1.1,min v.1.2 K),mem_carrierVertices.mpr
    ⟨(mem_carrierVertices.mp v.2).1,(mem_carrierVertices.mp v.2).2.1,
      (min_le_right _ _).trans (by omega)⟩⟩

theorem floorVertex_eq_self {K : ℕ} {A B : ℤ} (v : CarrierVertex (K+1) A B) (hv : v.1.2 ≤ K) :
    floorVertex v = v := by
  apply Subtype.ext
  simp only [floorVertex,min_eq_left hv,Prod.eta]
@[simp] theorem floorVertex_idem {K : ℕ} {A B : ℤ} (v : CarrierVertex (K+1) A B) :
    floorVertex (floorVertex v) = floorVertex v := floorVertex_eq_self _ (min_le_right _ _)

def verticalMap {K : ℕ} {A B : ℤ} (p : Probability (CarrierVertex (K+1) A B)) (t : unitInterval) :=
  Probability.mix p (Probability.push floorVertex p) t



theorem verticalMap_track {K : ℕ} {A B : ℤ} (p : Probability (CarrierVertex (K+1) A B)) :
    LipschitzWith 1 (verticalMap p) := by
  apply LipschitzWith.of_dist_le_mul
  intro r s
  change dist (FixedSlots.mix p.mass (Probability.push floorVertex p).mass r)
    (FixedSlots.mix p.mass (Probability.push floorVertex p).mass s) ≤ _
  exact (FixedSlots.mix_lipschitz _ _ 1 (Probability.dist_le_one _ _)).dist_le_mul r s

theorem verticalMap_joint {K : ℕ} {A B : ℤ} :
    LipschitzWith (2+Fintype.card (CarrierVertex (K+1) A B))
      (fun z : Probability (CarrierVertex (K+1) A B) × unitInterval => verticalMap z.1 z.2) := by
  apply LipschitzWith.of_dist_le_mul
  rintro ⟨p,t⟩ ⟨q,s⟩
  let N : ℝ := Fintype.card (CarrierVertex (K+1) A B)
  have hN : 0 ≤ N := Nat.cast_nonneg _
  have hd : 0 ≤ dist p q := dist_nonneg
  have hpush : dist (Probability.push floorVertex p) (Probability.push floorVertex q) ≤ N*dist p q :=
    (Probability.push_lipschitz floorVertex).dist_le_mul p q
  have hspace : dist (verticalMap p t) (verticalMap q t) ≤ (1+N)*dist p q := by
    apply FixedSlots.mix_dist_le_of_le (a := p.mass) (b := q.mass)
      (c := (Probability.push floorVertex p).mass) (d := (Probability.push floorVertex q).mass)
    · change dist p q ≤ (1+N)*dist p q; nlinarith
    · change dist (Probability.push floorVertex p) (Probability.push floorVertex q) ≤ (1+N)*dist p q
      nlinarith
  have htime := (verticalMap_track q).dist_le_mul t s
  have hpq : dist p q ≤ dist (p,t) (q,s) := by simp only [Prod.dist_eq]; exact le_max_left _ _
  have hts : dist t s ≤ dist (p,t) (q,s) := by simp only [Prod.dist_eq]; exact le_max_right _ _
  have htri := dist_triangle (verticalMap p t) (verticalMap q t) (verticalMap q s)
  change dist (verticalMap p t) (verticalMap q s) ≤ (2+N)*dist (p,t) (q,s)
  norm_num at htime
  nlinarith

def fanOriginal {m K t : ℕ} {A B : ℤ} (p : SimplicialCarrier (fanFaces m K A B t)) :
    Realization m (K+1) A B := by
  refine ⟨p.1,?_⟩
  obtain ⟨s,hs,hp⟩ := p.2
  exact ⟨s,((mem_fanFaces s).mp hs).1,hp⟩

theorem terminal_fan_vertical_support {m K : ℕ} {A B : ℤ} (hm : 1 ≤ m)
    (p : SimplicialCarrier (fanFaces m K A B 0)) (v : CarrierVertex (K+1) A B)
    (hvpos : 0 < p.1.mass v) (hvtop : v.1.2 = K+1) :
    p.1.SupportedOn ({floorVertex v,v} : Set _) := by
  obtain ⟨hs,hallowed⟩ := (mem_fanFaces _).mp (positiveSupport_mem_fan p)
  have hs' := (mem_simplexFaces _).mp hs
  have hv' := (mem_positiveSupport_image p.1 v).mpr hvpos
  have hsub := top_face_vertical hm hs' hallowed hv' hvtop
  intro w hw
  have hw' := hsub ((mem_positiveSupport_image p.1 w).mpr hw)
  simp only [verticalPair,Finset.mem_insert,Finset.mem_singleton] at hw'
  rcases hw' with h | h
  · have hwf : w = floorVertex v := by
      apply Subtype.ext
      simpa only [floorVertex,hvtop,min_eq_right (by omega : K ≤ K+1)] using h
    simp [hwf]
  · have hwv : w = v := by
      apply Subtype.ext
      exact h.trans (Prod.ext rfl hvtop.symm)
    simp [hwv]

theorem terminal_fan_verticalMap_mem {m K : ℕ} {A B : ℤ} (hm : 1 ≤ m)
    (p : SimplicialCarrier (fanFaces m K A B 0)) (t : unitInterval) :
    InRealization m (K+1) A B (verticalMap p.1 t) := by
  by_cases h : ∃ v : CarrierVertex (K+1) A B, 0 < p.1.mass v ∧ v.1.2 = K+1
  · obtain ⟨v,hvpos,hvtop⟩ := h
    have hp := terminal_fan_vertical_support hm p v hvpos hvtop
    have hq : (Probability.push floorVertex p.1).SupportedOn ({floorVertex v,v} : Set _) := by
      intro w hw
      obtain ⟨u,hu,hup⟩ := (Probability.push_pos_iff floorVertex p.1 w).mp hw
      have hu' := hp u hup
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hu'
      rcases hu' with huf | huv
      · subst u; simp only [floorVertex_idem] at hu; simp [←hu]
      · subst u; simp [←hu]
    refine ⟨{floorVertex v,v},?_,?_⟩
    · apply (mem_simplexFaces _).mpr
      refine Or.inr (Or.inl ⟨(floorVertex v).1,(floorVertex v).2,v.1,v.2,?_,?_⟩)
      · apply vertical_adj
        change v.1 = ((floorVertex v).1.1,(floorVertex v).1.2+1)
        apply Prod.ext
        · rfl
        · simp [floorVertex,hvtop]
      · simp
    · simpa using Probability.supportedOn_mix hp hq t
  · have hfix : Probability.push floorVertex p.1 = p.1 := by
      apply Probability.push_eq_self
      intro v hv
      apply floorVertex_eq_self
      have hbound := (mem_carrierVertices.mp v.2).2.2
      have hn : v.1.2 ≠ K+1 := fun he => h ⟨v,hv,he⟩
      omega
    simpa only [verticalMap,hfix,Probability.mix_self] using (fanOriginal p).2

def collapseVertical {m K : ℕ} {A B : ℤ} (hm : 1 ≤ m)
    (p : SimplicialCarrier (fanFaces m K A B 0)) (t : unitInterval) : Realization m (K+1) A B :=
  ⟨verticalMap p.1 t,terminal_fan_verticalMap_mem hm p t⟩




@[simp] theorem collapseVertical_zero {m K : ℕ} {A B : ℤ} (hm : 1 ≤ m)
    (p : SimplicialCarrier (fanFaces m K A B 0)) : collapseVertical hm p 0 = fanOriginal p :=
  Subtype.ext (Probability.mix_zero _ _)

theorem collapseVertical_terminal_height {m K : ℕ} {A B : ℤ} (hm : 1 ≤ m)
    (p : SimplicialCarrier (fanFaces m K A B 0)) (v : CarrierVertex (K+1) A B)
    (hv : 0 < (collapseVertical hm p 1).1.mass v) : v.1.2 ≤ K := by
  change 0 < (Probability.mix p.1 (Probability.push floorVertex p.1) 1).mass v at hv
  rw [Probability.mix_one] at hv
  obtain ⟨u,hu,hup⟩ := (Probability.push_pos_iff floorVertex p.1 v).mp hv
  rw [←hu]
  exact min_le_right _ _

end
end AbelianTargets.IntervalCarriers


