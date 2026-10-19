-- Prove2me | solution 1 for AbelianTargets.LowerCellCarrierMaps.boundaryValue_translate
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-19T03:54:26.355824+00:00
-- url     : https://prove2.me/submissions/ddd5cd31-6fec-4511-a895-2963c70f7d58

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_AnisotropicMarkers
import Definitions.Def_AT260939824_AtlasBoundaryCarrierMaps
import Definitions.Def_AT260939824_AtlasBoundaryTranslation
import Definitions.Def_AT260939824_AtlasBoxes
import Definitions.Def_AT260939824_AtlasRankRecursion
import Definitions.Def_AT260939824_CarrierCellRealization
import Definitions.Def_AT260939824_CarrierGeometry
import Definitions.Def_AT260939824_CarrierIntervalInclusion
import Definitions.Def_AT260939824_CarrierTranslationGeometry
import Definitions.Def_AT260939824_ClopenMarkers
import Definitions.Def_AT260939824_CompressedWords
import Definitions.Def_AT260939824_ConeDomainNaturality
import Definitions.Def_AT260939824_ContinuousAtlasPatterns
import Definitions.Def_AT260939824_ContinuousMarkerBoxes
import Definitions.Def_AT260939824_ControlledCone
import Definitions.Def_AT260939824_CovariantCuts
import Definitions.Def_AT260939824_DigitPathRealization
import Definitions.Def_AT260939824_Dimension
import Definitions.Def_AT260939824_FiniteRectangleIntersections
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
import Definitions.Def_AT260939824_ProbabilityPushGeometry
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

set_option autoImplicit false

-- Preserved source skeleton: AbelianTargets.AtlasBoundaryTranslation
section
namespace AbelianTargets
noncomputable section
variable {d : ℕ} {m K : ℕ} {i : Fin d}





theorem closedBox_subset_translate {Q R : RectangularCell d} (a : Fin d→ℤ)
    (hQR : Q.closedBox⊆R.closedBox) : (Q.translate a).closedBox⊆(R.translate a).closedBox := by
  intro z hz
  have hQ := (Q.mem_closedBox_translateCoordinates a (translateCoordinates (-a) z)).mp
    (by simpa using hz)
  have hR := (R.mem_closedBox_translateCoordinates a (translateCoordinates (-a) z)).mpr (hQR hQ)
  simpa using hR

theorem cellIntervalInclude_translate {Q R : RectangularCell d} (a : Fin d→ℤ)
    (hQR : Q.closedBox⊆R.closedBox) (p : CellIntervalCarrier m K i Q) :
    cellIntervalTranslate i a R (cellIntervalInclude i hQR p)=
      cellIntervalInclude i (closedBox_subset_translate a hQR) (cellIntervalTranslate i a Q p) := by
  apply Subtype.ext
  change Probability.push _ (Probability.push _ p.val)=Probability.push _ (Probability.push _ p.val)
  rw [Probability.push_comp,Probability.push_comp]
  rfl





namespace IntegerRectangularTiling
variable {K₀ : Fin d→ℕ} (T : IntegerRectangularTiling d K₀)



end IntegerRectangularTiling

namespace LowerCellCarrierMaps
variable {K₀ : Fin d→ℕ} {T : IntegerRectangularTiling d K₀} {R : RectangularCell d}



end LowerCellCarrierMaps
end
end AbelianTargets

end

namespace AbelianTargets
end AbelianTargets
open AbelianTargets
variable {d : ℕ} {m K : ℕ} {i : Fin d}
namespace AbelianTargets.LowerCellCarrierMaps
end AbelianTargets.LowerCellCarrierMaps
open AbelianTargets
open AbelianTargets.LowerCellCarrierMaps
variable {K₀ : Fin d→ℕ} {T : IntegerRectangularTiling d K₀} {R : RectangularCell d}

theorem solution (F : LowerCellCarrierMaps T m K i R) (hR : R∈T.cells)
    (a : Fin d→ℤ) (G : LowerCellCarrierMaps (T.translate a) m K i (R.translate a))
    (hmap : ∀ (Q : RectangularCell d) (hQ : Q∈T.cells) (hr : Q.rank<R.rank)
      (z : CellClosedDomain Q),
      G.map (Q.translate a) (T.cell_translate hQ a)
        (by simpa only [RectangularCell.rank_translate] using hr) (Q.translateClosedPoint a z)=
        cellIntervalTranslate i a Q (F.map Q hQ hr z))
    (z : CellBoundaryDomain R) :
    G.boundaryValue (T.cell_translate hR a) (R.translateBoundaryPoint a z)=
      cellIntervalTranslate i a R (F.boundaryValue hR z) := by
  let Q := T.pointCell z.val
  have hQ : Q∈T.cells := ⟨z.val,rfl⟩
  have hr : Q.rank<R.rank := T.pointCell_rank_lt_cell_boundary hR z.property
  have hQR := T.pointCell_subset_cell hR z.property.1
  have hzQ : z.val∈Q.closedBox := Q.relativeInterior_subset (T.mem_relativeInterior_pointCell z.val)
  have hQ' := T.cell_translate hQ a
  have hr' : (Q.translate a).rank<(R.translate a).rank := by
    simpa only [RectangularCell.rank_translate] using hr
  have hQR' := closedBox_subset_translate a hQR
  have hzQ' : (R.translateBoundaryPoint a z).val∈(Q.translate a).closedBox :=
    (Q.mem_closedBox_translateCoordinates a z.val).mpr hzQ
  rw [G.boundaryValue_eq (T.cell_translate hR a) hQ' hr' hQR' _ hzQ']
  rw [F.boundaryValue_eq hR hQ hr hQR z hzQ]
  rw [cellIntervalInclude_translate]
  congr 1
  exact hmap Q hQ hr ⟨z.val,hzQ⟩
