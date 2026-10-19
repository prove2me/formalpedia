-- Prove2me | Definitions.Def_AT260939824_CarrierTranslationEquiv
-- name    : AT260939824_CarrierTranslationEquiv
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T03:16:30.354228+00:00
-- url     : https://prove2.me/theorems/41eb786f-0817-4610-9575-cbe4513d4754
-- title:
--   Translation isometries and transport of contractions
-- statement:
--   For an integer displacement $a$, horizontal vertex translation induces the isometric equivalence
--
--   $$ \mathcal C_m^K([A,B])\simeq\mathcal C_m^K([A+a,B+a]). $$
--
--   The inverse translates by $-a$. A controlled contraction transports along an isometric equivalence while retaining its track and joint constants. This allows a contraction selected on a zero-based interval to be used on any translated interval.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (2026), Section(s) 4; https://arxiv.org/abs/2609.39824v1. This item is auxiliary infrastructure of the accompanying formalization, not a claim that each implementation definition is separately numbered in the paper. Original Lean module AbelianTargets/CarrierTranslationEquiv.lean, selected declaration lines 10-14, 16-27, 29-49, 58-71; SHA-256 3093d9b04064a0e32164258396006532e9c553f7a299c12c41dcd46230255687. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_CarrierCellRealization
import Definitions.Def_AT260939824_CarrierGeometry
import Definitions.Def_AT260939824_CarrierTranslationGeometry
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

namespace AbelianTargets.IntervalCarriers
noncomputable section
attribute [local instance] Classical.propDecidable

def inverseVertexTranslation {K : ℕ} {A B : ℤ} (a : ℤ)
    (v : CarrierVertex K (A+a) (B+a)) : CarrierVertex K A B :=
  ⟨translate (-a) v.1,by
    have h := (translate_mem_carrierVertices (-a) v.1).mpr v.2
    simpa using h⟩

def inverseRealizationTranslation {m K : ℕ} {A B : ℤ} (a : ℤ)
    (p : Realization m K (A+a) (B+a)) : Realization m K A B := by
  refine ⟨Probability.push (inverseVertexTranslation a) p.1,?_⟩
  obtain ⟨s,hs,hp⟩ := p.2
  refine ⟨s.image (inverseVertexTranslation a),?_,?_⟩
  · apply (mem_simplexFaces _).mpr
    rw [Finset.image_image]
    have h := ((mem_simplexFaces s).mp hs).translated (-a)
    simpa only [add_neg_cancel_right,Finset.image_image,Function.comp_def] using h
  · intro w hw
    obtain ⟨v,hv,hvp⟩ := (Probability.push_pos_iff (inverseVertexTranslation a) p.1 w).mp hw
    exact Finset.mem_image.mpr ⟨v,hp v hvp,hv⟩

def realizationTranslationEquiv {m K : ℕ} {A B : ℤ} (a : ℤ) :
    Realization m K A B ≃ᵢ Realization m K (A+a) (B+a) where
  toFun := realizationTranslation a
  invFun := inverseRealizationTranslation a
  left_inv p := by
    apply Subtype.ext
    change Probability.push (inverseVertexTranslation a) (Probability.push (vertexTranslation a) p.1)=p.1
    rw [Probability.push_comp]
    apply Probability.push_eq_self
    intro v hv
    apply Subtype.ext
    simp [vertexTranslation,inverseVertexTranslation,translate]
  right_inv p := by
    apply Subtype.ext
    change Probability.push (vertexTranslation a) (Probability.push (inverseVertexTranslation a) p.1)=p.1
    rw [Probability.push_comp]
    apply Probability.push_eq_self
    intro v hv
    apply Subtype.ext
    simp [vertexTranslation,inverseVertexTranslation,translate]
  isometry_toFun := realizationTranslation_isometry a

end
end AbelianTargets.IntervalCarriers

namespace AbelianTargets.ControlledContraction
open scoped NNReal unitInterval
noncomputable section

def transport {Z W : Type*} [MetricSpace Z] [MetricSpace W] {p : Z} {D J : ℝ≥0}
    (H : ControlledContraction p D J) (e : Z ≃ᵢ W) : ControlledContraction (e p) D J where
  map z := e (H.map (e.symm z.1,z.2))
  continuous := e.continuous.comp (H.continuous.comp ((e.symm.continuous.comp continuous_fst).prodMk continuous_snd))
  at_zero z := by rw [H.at_zero,e.apply_symm_apply]
  at_one z := by rw [H.at_one]
  fixes t := by rw [e.symm_apply_apply,H.fixes]
  track z := by simpa only [Function.comp_def,one_mul] using e.isometry.lipschitz.comp (H.track (e.symm z))
  joint := by
    have hp : LipschitzWith 1 (fun z : W × I => (e.symm z.1,z.2)) := by
      simpa only [Function.comp_def,one_mul,max_self] using
        (e.symm.isometry.lipschitz.comp LipschitzWith.prod_fst).prodMk
          (LipschitzWith.prod_snd : LipschitzWith 1 (Prod.snd : W × I → I))
    simpa only [Function.comp_def,mul_one,one_mul] using e.isometry.lipschitz.comp (H.joint.comp hp)

end
end AbelianTargets.ControlledContraction


