-- Prove2me | solution 1 for AbelianTargets.PrismBoundaryData.fill_translate_of_maps
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-19T03:56:06.031268+00:00
-- url     : https://prove2.me/submissions/40aa012e-7aef-4c54-9789-f486df0cb0e2

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_AnisotropicMarkers
import Definitions.Def_AT260939824_AtlasBoundaryCarrierMaps
import Definitions.Def_AT260939824_AtlasBoxes
import Definitions.Def_AT260939824_AtlasRankRecursion
import Definitions.Def_AT260939824_CarrierCellRealization
import Definitions.Def_AT260939824_CarrierGeometry
import Definitions.Def_AT260939824_CarrierIntervalInclusion
import Definitions.Def_AT260939824_CarrierTranslationEquiv
import Definitions.Def_AT260939824_ClopenMarkers
import Definitions.Def_AT260939824_CompressedWords
import Definitions.Def_AT260939824_ConeDomainNaturality
import Definitions.Def_AT260939824_ContinuousAtlasPatterns
import Definitions.Def_AT260939824_ContinuousMarkerBoxes
import Definitions.Def_AT260939824_ControlledCone
import Definitions.Def_AT260939824_CovariantCuts
import Definitions.Def_AT260939824_DigitPathRealization
import Definitions.Def_AT260939824_Dimension
import Definitions.Def_AT260939824_FixedSlotInterpolation
import Definitions.Def_AT260939824_IntegerGridIntervals
import Definitions.Def_AT260939824_IntegerPrismChart
import Definitions.Def_AT260939824_IntegerPrismFilling
import Definitions.Def_AT260939824_IntegerPrismTranslation
import Definitions.Def_AT260939824_IntervalCarriers
import Definitions.Def_AT260939824_MarkerExistence
import Definitions.Def_AT260939824_MarkerMap
import Definitions.Def_AT260939824_MarkerPriorities
import Definitions.Def_AT260939824_MarkerWindows
import Definitions.Def_AT260939824_OrbitMarkerCuts
import Definitions.Def_AT260939824_ParityCoordinates
import Definitions.Def_AT260939824_ParityFields
import Definitions.Def_AT260939824_PriorityCuts
import Definitions.Def_AT260939824_Probability
import Definitions.Def_AT260939824_ProbabilityMap
import Definitions.Def_AT260939824_RectangularAtlasBoundary
import Definitions.Def_AT260939824_RectangularBoundaryStrata
import Definitions.Def_AT260939824_RectangularCells
import Definitions.Def_AT260939824_RectangularCone
import Definitions.Def_AT260939824_RectangularTranslation
import Definitions.Def_AT260939824_RegularAnisotropicAtlas
import Definitions.Def_AT260939824_RelativeContractionNaturality
import Definitions.Def_AT260939824_RelativePathContraction
import Definitions.Def_AT260939824_Rounding
import Definitions.Def_AT260939824_SupportGeometry
import Definitions.Def_AT260939824_SupportModel
import Init
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Algebra.Group.Conj
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Prod
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
import Mathlib.Data.Countable.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Preimage
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Interval
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Dynamics.Transitive
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Order.Filter.Finite
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Clopen
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.Constructions
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Homotopy.Path
import Mathlib.Topology.Instances.Discrete
import Mathlib.Topology.Instances.Int
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.LocallyFinite
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
import Theorems.Thm_AbelianTargets_RectangularCell_prismCoordinates_translate

set_option autoImplicit false

-- Preserved source skeleton: AbelianTargets.RelativeContractionNaturality
section
/-! The literal relative homotopy and cone filling commute with isometric
transport. These equalities concern the actual formulas, including all
four path deformation stages and the radial extension. -/

namespace AbelianTargets.ControlledContraction
open scoped unitInterval NNReal
noncomputable section
variable {Z W : Type*} [MetricSpace Z] [MetricSpace W]
variable {p q : Z} {D J S B : ℝ≥0}
variable (H : ControlledContraction p D J) (e : Z ≃ᵢ W)





theorem transport_compressRaw (P : Path p q) (z : I × ℝ) :
    compressRaw (P.map e.continuous) z=e (compressRaw P z) := rfl

theorem transport_spurRaw (P : Path p q) (z : I × ℝ) :
    (H.transport e).spurRaw (P.map e.continuous) z=e (H.spurRaw P z) := by
  unfold spurRaw slot3
  split_ifs <;> simp [transport]

theorem transport_thirdRaw (P : Path p q) (z : I × ℝ) :
    (H.transport e).thirdRaw (P.map e.continuous) z=e (H.thirdRaw P z) := by
  unfold thirdRaw slot3
  split_ifs <;> simp [transport]

theorem transport_expandRaw (z : I × ℝ) :
    (H.transport e).expandRaw (e q) z=e (H.expandRaw q z) := by
  simp [expandRaw]

theorem transport_relativeHomotopy (P : Path p q) (z : I × I) :
    (H.transport e).relativeHomotopy (P.map e.continuous) z=
      e (H.relativeHomotopy P z) := by
  simp only [relativeHomotopy,Path.Homotopy.trans_apply]
  split_ifs <;>
    simp only [compressionHomotopy,spurHomotopy,thirdHomotopy,expansionHomotopy,
      transport_compressRaw,transport_spurRaw,transport_thirdRaw,transport_expandRaw] <;> rfl

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]



theorem transport_coneValue (F : BoundaryPathFamily (E := E) p q S B)
    (x : ConeBall E) (u : I) :
    (H.transport e).coneValue (F.transport e) x u=e (H.coneValue F x u) := by
  unfold coneValue
  split_ifs
  · exact H.transport_relativeHomotopy e _ _
  · exact H.transport_shortPath e u

end
end AbelianTargets.ControlledContraction

end

-- Preserved source skeleton: AbelianTargets.ConeDomainNaturality
section
/-! The relative cone formula respects linear isometries of the transverse
coordinate space. In particular, a relabeling of active rectangular axes
does not change the filling. -/

namespace AbelianTargets
open scoped unitInterval NNReal
noncomputable section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]





theorem radialDirection_linearIsometry (k : E ≃ₗᵢ[ℝ] F) (x : E) (hx : 0<‖x‖) :
    radialDirection (k x) (by simpa using hx)=coneSphereMap k (radialDirection x hx) := by
  apply Subtype.ext
  simp [radialDirection,coneSphereMap]



namespace ControlledContraction
variable {Z : Type*} [MetricSpace Z] {p q : Z} {D J S B : ℝ≥0}
variable (H : ControlledContraction p D J)





end ControlledContraction
end
end AbelianTargets

end

-- Preserved source skeleton: AbelianTargets.IntegerPrismTranslation
section
set_option backward.isDefEq.respectTransparency false

namespace AbelianTargets.RectangularCell
noncomputable section
open scoped unitInterval
variable {d : ℕ}























theorem normalizeTransverse_translate (R : RectangularCell d) (a : Fin d→ℤ) (i : Fin d)
    (z : CellClosedDomain R) :
    (R.translate a).normalizeTransverse i (R.translateClosedPoint a z)=
      R.translateConeBall a i (R.normalizeTransverse i z) := by
  apply Subtype.ext
  funext j
  simp only [normalizeTransverse,transverseWidth_translate]
  change (2*(z.val j.val+(a j.val : ℝ))-((R.lower j.val+a j.val : ℤ) : ℝ)-
      ((R.upper j.val+a j.val : ℤ) : ℝ))/R.transverseWidth j.val=
      (2*z.val j.val-(R.lower j.val : ℝ)-(R.upper j.val : ℝ))/R.transverseWidth j.val
  push_cast
  ring

theorem firstIntervalParameter_translate (R : RectangularCell d) (a : Fin d→ℤ) (i : Fin d)
    (hi : R.lower i<R.upper i) (z : CellClosedDomain R) :
    (R.translate a).firstIntervalParameter i (by simpa [translate] using hi) (R.translateClosedPoint a z)=
      R.firstIntervalParameter i hi z := by
  apply Subtype.ext
  simp only [firstIntervalParameter,transverseWidth_translate]
  change (z.val i+(a i : ℝ)-((R.lower i+a i : ℤ) : ℝ))/R.transverseWidth i=
    (z.val i-(R.lower i : ℝ))/R.transverseWidth i
  push_cast
  ring

end
end AbelianTargets.RectangularCell

end

-- Preserved source skeleton: AbelianTargets.IntegerPrismFillTranslation
section
namespace AbelianTargets
noncomputable section
open scoped NNReal unitInterval
variable {d : ℕ}

theorem prismBoundaryPoint_translate (R : RectangularCell d) (a : Fin d→ℤ) (i : Fin d)
    (v : ConeSphere (R.ActiveTransverse i→ℝ)) (r : I) :
    prismBoundaryPoint (R.translate a) i (R.translateConeSphere a i v) r=
      R.translateBoundaryPoint a (prismBoundaryPoint R i v r) := by
  apply Subtype.ext
  exact R.prismCoordinates_translate a i r ⟨v.val,v.property.le⟩

namespace PrismBoundaryData
variable {Z W : Type*} [MetricSpace Z] [MetricSpace W]
variable {R : RectangularCell d} {i : Fin d} {p q : Z} {D J S B : ℝ≥0}





end PrismBoundaryData
end
end AbelianTargets

end

-- Preserved source skeleton: AbelianTargets.PrismFillNaturality
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace AbelianTargets
noncomputable section
open scoped NNReal unitInterval

namespace ControlledContraction
variable {E F Z W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [MetricSpace Z] [MetricSpace W]
variable {p q : Z} {D J S B S' B' : ℝ≥0}

theorem coneValue_transport_domain_natural_any_bounds (H : ControlledContraction p D J)
    (e : Z≃ᵢW) (k : E≃ₗᵢ[ℝ]F)
    (P : BoundaryPathFamily (E := E) p q S B)
    (Q : BoundaryPathFamily (E := F) (e p) (e q) S' B')
    (hpaths : ∀v,Q.path (coneSphereMap k v)=(P.path v).map e.continuous)
    (x : ConeBall E) (u : I) :
    (H.transport e).coneValue Q (coneBallMap k x) u=e (H.coneValue P x u) := by
  have hh : (H.transport e).coneValue Q (coneBallMap k x) u=
      (H.transport e).coneValue (P.transport e) x u := by
    have hnorm : ‖(coneBallMap k x).val‖=‖x.val‖ := k.norm_map x.val
    by_cases hx : (1/2 : ℝ)≤‖x.val‖
    · have hx' : (1/2 : ℝ)≤‖(coneBallMap k x).val‖ := by rw [hnorm];exact hx
      rw [coneValue,dif_pos hx',coneValue,dif_pos hx]
      have hdir : radialDirection (coneBallMap k x).val (by linarith)=
          coneSphereMap k (radialDirection x.val (by linarith)) := by
        change radialDirection (k x.val) _=coneSphereMap k (radialDirection x.val _)
        exact radialDirection_linearIsometry k x.val (by linarith)
      rw [hdir,hpaths,coneParameter_linearIsometry]
      rfl
    · have hx' : ¬(1/2 : ℝ)≤‖(coneBallMap k x).val‖ := by rw [hnorm];exact hx
      rw [coneValue,dif_neg hx',coneValue,dif_neg hx]
  exact hh.trans (H.transport_coneValue e P x u)

theorem ext_map {p : Z} (H G : ControlledContraction p D J) (h : H.map=G.map) : H=G := by
  cases H
  cases G
  cases h
  rfl

end ControlledContraction

namespace PrismBoundaryData
variable {d : ℕ} {Z W : Type*} [MetricSpace Z] [MetricSpace W]
variable {R : RectangularCell d} {i : Fin d} {p q : Z} {p' q' : W}
variable {D J S B S' B' : ℝ≥0}



end PrismBoundaryData
end
end AbelianTargets

end

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace AbelianTargets
end AbelianTargets
open AbelianTargets
open scoped NNReal unitInterval
namespace AbelianTargets.PrismBoundaryData
end AbelianTargets.PrismBoundaryData
open AbelianTargets
open AbelianTargets.PrismBoundaryData
variable {d : ℕ} {Z W : Type*} [MetricSpace Z] [MetricSpace W]
variable {R : RectangularCell d} {i : Fin d} {p q : Z} {p' q' : W}
variable {D J S B S' B' : ℝ≥0}

theorem solution (F : PrismBoundaryData R i p q S B)
    (H : ControlledContraction p D J) (a : Fin d→ℤ) (e : Z≃ᵢW)
    (G : PrismBoundaryData (R.translate a) i p' q' S' B')
    (H' : ControlledContraction p' D J) (hp : e p=p') (hq : e q=q')
    (hH : ∀v t,H'.map (e v,t)=e (H.map (v,t)))
    (hmap : ∀z : CellBoundaryDomain R,G.map (R.translateBoundaryPoint a z)=e (F.map z))
    (hi : R.lower i<R.upper i) (z : CellClosedDomain R) :
    G.fill H' (by simpa [RectangularCell.translate] using hi) (R.translateClosedPoint a z)=
      e (F.fill H hi z) := by
  subst p'
  subst q'
  have hHeq : H'=H.transport e := by
    apply ControlledContraction.ext_map
    funext v
    have hh := hH (e.symm v.1) v.2
    simpa only [e.apply_symm_apply,ControlledContraction.transport] using hh
  rw [hHeq]
  let k := R.activeLinearTranslation a i
  have hsphere : ∀v : ConeSphere (R.ActiveTransverse i→ℝ),
      coneSphereMap k v=R.translateConeSphere a i v := fun _=>rfl
  have hball : ∀v : ConeBall (R.ActiveTransverse i→ℝ),
      coneBallMap k v=R.translateConeBall a i v := fun _=>rfl
  have hpaths : ∀v,G.pathFamily.path (coneSphereMap k v)=(F.pathFamily.path v).map e.continuous := by
    intro v
    apply Path.ext
    funext r
    change G.map (prismBoundaryPoint (R.translate a) i (coneSphereMap k v) r)=
      e (F.map (prismBoundaryPoint R i v r))
    rw [hsphere,prismBoundaryPoint_translate]
    exact hmap _
  unfold fill
  rw [R.normalizeTransverse_translate,R.firstIntervalParameter_translate,←hball]
  exact H.coneValue_transport_domain_natural_any_bounds e k F.pathFamily G.pathFamily hpaths _ _
