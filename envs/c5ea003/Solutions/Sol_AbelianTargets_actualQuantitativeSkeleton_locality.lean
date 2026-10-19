-- Prove2me | solution 1 for AbelianTargets.actualQuantitativeSkeleton_locality
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-19T04:09:49.906615+00:00
-- url     : https://prove2.me/submissions/18bc100c-0f5e-4443-b129-5b22cf9da0f4

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_ActualQuantitativeAtlasRecursion
import Definitions.Def_AT260939824_AnisotropicMarkers
import Definitions.Def_AT260939824_AtlasBoundaryCarrierMaps
import Definitions.Def_AT260939824_AtlasBoundaryTransverseBounds
import Definitions.Def_AT260939824_AtlasBoxes
import Definitions.Def_AT260939824_AtlasCarrierEndpoints
import Definitions.Def_AT260939824_AtlasControlledCellExtension
import Definitions.Def_AT260939824_AtlasEndpointRecursion
import Definitions.Def_AT260939824_AtlasQuantitativeRecursion
import Definitions.Def_AT260939824_AtlasRankRecursion
import Definitions.Def_AT260939824_AtlasRelativeCellExtension
import Definitions.Def_AT260939824_CarrierCellRealization
import Definitions.Def_AT260939824_CarrierGeometry
import Definitions.Def_AT260939824_CarrierIntervalInclusion
import Definitions.Def_AT260939824_ClopenMarkers
import Definitions.Def_AT260939824_CompressedWords
import Definitions.Def_AT260939824_ConeDomainNaturality
import Definitions.Def_AT260939824_ContinuousAtlasPatterns
import Definitions.Def_AT260939824_ContinuousMarkerBoxes
import Definitions.Def_AT260939824_ControlledCone
import Definitions.Def_AT260939824_CovariantCuts
import Definitions.Def_AT260939824_DeterministicQuantitativeAtlas
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
import Definitions.Def_AT260939824_ProbabilityPushDirac
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
import Mathlib.Tactic.GCongr
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

set_option autoImplicit false

-- Preserved source skeleton: AbelianTargets.IntegerPrismFillTranslation
section
namespace AbelianTargets
noncomputable section
open scoped NNReal unitInterval
variable {d : ℕ}



namespace PrismBoundaryData
variable {Z W : Type*} [MetricSpace Z] [MetricSpace W]
variable {R : RectangularCell d} {i : Fin d} {p q : Z} {D J S B : ℝ≥0}



/-- The computed filling depends on the literal boundary values only.
Different certificates or numerical upper bounds do not affect the map. -/
theorem fill_ext {S' B' : ℝ≥0} (F : PrismBoundaryData R i p q S B)
    (G : PrismBoundaryData R i p q S' B') (H : ControlledContraction p D J)
    (hmap : ∀ z,F.map z=G.map z) (hi : R.lower i<R.upper i) (z : CellClosedDomain R) :
    F.fill H hi z=G.fill H hi z := by
  unfold fill ControlledContraction.coneValue
  split_ifs with hx
  · have hpath : F.pathFamily.path (radialDirection (R.normalizeTransverse i z).val (by linarith))=
        G.pathFamily.path (radialDirection (R.normalizeTransverse i z).val (by linarith)) := by
      apply Path.ext
      funext r
      exact hmap _
    rw [hpath]
  · rfl

end PrismBoundaryData
end
end AbelianTargets

end

-- Preserved source skeleton: AbelianTargets.AtlasCellLocality
section
namespace AbelianTargets
noncomputable section
open scoped NNReal
variable {d : ℕ} {K₀ : Fin d→ℕ} {T T' : IntegerRectangularTiling d K₀}
variable {m K : ℕ} {i : Fin d} {R : RectangularCell d}

namespace LowerCellCarrierMaps

/-- The boundary operator inspects only the finite actual boundary cells
of its parent. A different atlas agreeing on those cells gives the same value. -/
theorem boundaryValue_eq_of_finite_lower_agreement
    (F : LowerCellCarrierMaps T m K i R) (G : LowerCellCarrierMaps T' m K i R)
    (hR : R∈T.cells) (hR' : R∈T'.cells)
    (hcell : ∀ Q∈T.boundaryCells R,Q∈T'.cells)
    (hmap : ∀ (Q : RectangularCell d) (hQ : Q∈T.boundaryCells R)
      (hQc : Q∈T.cells) (hQc' : Q∈T'.cells) (hr : Q.rank<R.rank) (z : CellClosedDomain Q),
      F.map Q hQc hr z=G.map Q hQc' hr z)
    (z : CellBoundaryDomain R) : F.boundaryValue hR z=G.boundaryValue hR' z := by
  let Q := T.pointCell z.val
  have hQ : Q∈T.cells := ⟨z.val,rfl⟩
  have hr : Q.rank<R.rank := T.pointCell_rank_lt_cell_boundary hR z.property
  have hQR := T.pointCell_subset_cell hR z.property.1
  have hb : Q∈T.boundaryCells R := (T.mem_boundaryCells R Q).mpr ⟨hQ,hQR,hr⟩
  have hQ' := hcell Q hb
  have hzQ : z.val∈Q.closedBox := Q.relativeInterior_subset (T.mem_relativeInterior_pointCell z.val)
  rw [F.boundaryValue_eq hR hQ hr hQR z hzQ,G.boundaryValue_eq hR' hQ' hr hQR z hzQ]
  rw [hmap Q hb hQ hQ' hr ⟨z.val,hzQ⟩]

theorem controlledCellExtension_map_ext
    (F : LowerCellCarrierMaps T m K i R) (G : LowerCellCarrierMaps T' m K i R)
    (hR : R∈T.cells) (hR' : R∈T'.cells) (hF : F.EndpointValues) (hG : G.EndpointValues)
    (C C' : Fin d→ℝ≥0) (hC : F.CoordinateBounds C) (hC' : G.CoordinateBounds C')
    (hi : R.lower i<R.upper i) {D J : ℝ≥0}
    (H : ControlledContraction (cellLeftPoint m K i R) D J)
    (hmap : ∀ z : CellBoundaryDomain R,F.boundaryValue hR z=G.boundaryValue hR' z)
    (z : CellClosedDomain R) :
    (F.controlledCellExtension hR hF C hC hi H).map z=
      (G.controlledCellExtension hR' hG C' hC' hi H).map z :=
  (F.controlledPrismData hR hF C hC hi).fill_ext
    (G.controlledPrismData hR' hG C' hC' hi) H hmap hi z

end LowerCellCarrierMaps
end
end AbelianTargets

end

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace AbelianTargets
end AbelianTargets
open AbelianTargets
open scoped NNReal
variable {d : ℕ} {K₀ : Fin d→ℕ} {T T' : IntegerRectangularTiling d K₀}
variable {m K : ℕ} {i : Fin d}

theorem solution
    (δ U : Fin d→ℝ≥0) (D J : ℝ≥0) (hδ : ∀j,0<δ j)
    (hlower : ∀R,R∈T.cells → ∀j,R.lower j<R.upper j → δ j≤(R.transverseWidth j).toNNReal)
    (hupper : ∀R,R∈T.cells → ∀j,(R.transverseWidth j).toNNReal≤U j)
    (hlower' : ∀R,R∈T'.cells → ∀j,R.lower j<R.upper j → δ j≤(R.transverseWidth j).toNNReal)
    (hupper' : ∀R,R∈T'.cells → ∀j,(R.transverseWidth j).toNNReal≤U j)
    (H : ∀R,R∈T.cells → R.lower i<R.upper i → ControlledContraction (cellLeftPoint m K i R) D J)
    (H' : ∀R,R∈T'.cells → R.lower i<R.upper i → ControlledContraction (cellLeftPoint m K i R) D J)
    (P : RectangularCell d)
    (hcells : ∀Q,Q.closedBox⊆P.closedBox → (Q∈T.cells ↔ Q∈T'.cells))
    (hH : ∀Q (hQ : Q∈T.cells) (hQ' : Q∈T'.cells) (hi : Q.lower i<Q.upper i),
      Q.closedBox⊆P.closedBox → H Q hQ hi=H' Q hQ' hi)
    (n : ℕ) : ∀ (R : RectangularCell d) (hR : R∈T.cells) (hR' : R∈T'.cells)
      (hr : R.rank<n) (hRP : R.closedBox⊆P.closedBox) (z : CellClosedDomain R),
      (actualQuantitativeSkeleton δ U D J hδ hlower hupper H n).map R hR hr z=
        (actualQuantitativeSkeleton δ U D J hδ hlower' hupper' H' n).map R hR' hr z := by
  induction n with
  | zero => intro R hR hR' hr; exact (Nat.not_lt_zero _ hr).elim
  | succ n ih =>
    intro R hR hR' hr hRP z
    let F := actualQuantitativeSkeleton δ U D J hδ hlower hupper H n
    let G := actualQuantitativeSkeleton δ U D J hδ hlower' hupper' H' n
    change F.toEndpointSkeletonCarrierMaps.nextMap (actualQuantitativeExtension F H) R hR hr z=
      G.toEndpointSkeletonCarrierMaps.nextMap (actualQuantitativeExtension G H') R hR' hr z
    by_cases hsmall : R.rank<n
    · simp only [EndpointSkeletonCarrierMaps.nextMap,dif_pos hsmall]
      exact ih R hR hR' hsmall hRP z
    · have he : R.rank=n := by omega
      simp only [EndpointSkeletonCarrierMaps.nextMap,dif_neg hsmall]
      by_cases hi : R.lower i<R.upper i
      · simp only [actualQuantitativeExtension,dif_pos hi]
        rw [←hH R hR hR' hi hRP]
        let LF := F.toSkeletonCarrierMaps.lowerFamily R he
        let LG := G.toSkeletonCarrierMaps.lowerFamily R he
        apply LF.controlledCellExtension_map_ext LG hR hR'
          (F.toEndpointSkeletonCarrierMaps.lowerFamily_endpoints R he)
          (G.toEndpointSkeletonCarrierMaps.lowerFamily_endpoints R he)
          _ _ (F.lowerFamily_update_bounds R he) (G.lowerFamily_update_bounds R he) hi (H R hR hi) _ z
        intro zb
        apply LF.boundaryValue_eq_of_finite_lower_agreement LG hR hR'
        · intro Q hQb
          obtain ⟨hQc,hQR,hrQ⟩ := (T.mem_boundaryCells R Q).mp hQb
          exact (hcells Q (hQR.trans hRP)).mp hQc
        · intro Q hQb hQc hQc' hrQ zQ
          have hQR := ((T.mem_boundaryCells R Q).mp hQb).2.1
          exact ih Q hQc hQc' (by omega) (hQR.trans hRP) zQ
      · simp only [actualQuantitativeExtension,dif_neg hi]
        rfl
