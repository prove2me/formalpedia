-- Prove2me | Definitions.Def_AT260939824_IntegerPrismEstimates
-- name    : AT260939824_IntegerPrismEstimates
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T03:03:22.360141+00:00
-- url     : https://prove2.me/theorems/869e04bb-c442-4f70-954e-1777b494b3e8
-- title:
--   Coordinate estimates for rectangular prism filling
-- statement:
--   In a rectangular cell $R$, normalized first-coordinate distance is the coordinate displacement divided by its width, while each active transverse coordinate has normalization bound twice the reciprocal width. These identities transfer the controlled contraction estimates to the actual prism filling. The bundle records separate first and transverse coordinate bounds, together with the fact that changing only a collapsed coordinate cannot change a point of the cell.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Sections 2-7; https://arxiv.org/html/2609.39824v1. Formalization-specific infrastructure in the import closure of Theorem 1.4 and Proposition 7.1; individual helper assertions are not represented as separately numbered paper theorems. Original Lean module AbelianTargets/IntegerPrismEstimates.lean, selected declaration lines 10-15, 17-26, 28-32, 34-54, 56-68, 77-86, 88-105; SHA-256 fedb6058548aa1e29a4fd1759dd6ff8813dc02cac82f23957023233921cf7bb0. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_AnisotropicMarkers
import Definitions.Def_AT260939824_AtlasBoundaryCarrierMaps
import Definitions.Def_AT260939824_AtlasBoxes
import Definitions.Def_AT260939824_AtlasRankRecursion
import Definitions.Def_AT260939824_CarrierCellRealization
import Definitions.Def_AT260939824_CarrierGeometry
import Definitions.Def_AT260939824_CarrierIntervalInclusion
import Definitions.Def_AT260939824_ClopenMarkers
import Definitions.Def_AT260939824_CompressedWords
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

namespace AbelianTargets
noncomputable section
open scoped unitInterval NNReal
variable {d : ℕ}

namespace RectangularCell

theorem normalizeTransverse_eq_of_except_first (R : RectangularCell d) (i : Fin d)
    (z z' : CellClosedDomain R) (heq : ∀ j,j≠i → z.val j=z'.val j) :
    R.normalizeTransverse i z=R.normalizeTransverse i z' := by
  apply Subtype.ext
  funext j
  simp only [normalizeTransverse,heq j.val j.property.1]

theorem firstIntervalParameter_dist (R : RectangularCell d) (i : Fin d)
    (hi : R.lower i<R.upper i) (z z' : CellClosedDomain R) :
    dist (R.firstIntervalParameter i hi z) (R.firstIntervalParameter i hi z')=
      |z.val i-z'.val i|/R.transverseWidth i := by
  have hw : 0<R.transverseWidth i := sub_pos.mpr (by exact_mod_cast hi)
  rw [Subtype.dist_eq,Real.dist_eq]
  change |(z.val i-(R.lower i : ℝ))/R.transverseWidth i-
      (z'.val i-(R.lower i : ℝ))/R.transverseWidth i|=_
  rw [←sub_div,show z.val i-(R.lower i : ℝ)-(z'.val i-(R.lower i : ℝ))=
    z.val i-z'.val i by ring,abs_div,abs_of_pos hw]

theorem firstIntervalParameter_eq (R : RectangularCell d) (i : Fin d)
    (hi : R.lower i<R.upper i) (z z' : CellClosedDomain R) (heq : z.val i=z'.val i) :
    R.firstIntervalParameter i hi z=R.firstIntervalParameter i hi z' := by
  apply Subtype.ext
  simp only [firstIntervalParameter,heq]

theorem normalizeTransverse_coordinate_dist_le (R : RectangularCell d) (i j : Fin d)
    (hj : R.lower j<R.upper j) (z z' : CellClosedDomain R)
    (heq : ∀ k,k≠j → z.val k=z'.val k) :
    dist (R.normalizeTransverse i z) (R.normalizeTransverse i z')≤
      (2/R.transverseWidth j)*|z.val j-z'.val j| := by
  have hw : 0<R.transverseWidth j := sub_pos.mpr (by exact_mod_cast hj)
  rw [Subtype.dist_eq]
  apply (dist_pi_le_iff (by positivity)).mpr
  intro k
  by_cases hkj : k.val=j
  · change |(2*z.val k.val-(R.lower k.val : ℝ)-(R.upper k.val : ℝ))/R.transverseWidth k.val-
      (2*z'.val k.val-(R.lower k.val : ℝ)-(R.upper k.val : ℝ))/R.transverseWidth k.val|≤_
    rw [hkj]
    have hsub : (2*z.val j-(R.lower j : ℝ)-(R.upper j : ℝ))/R.transverseWidth j-
        (2*z'.val j-(R.lower j : ℝ)-(R.upper j : ℝ))/R.transverseWidth j=
        (2/R.transverseWidth j)*(z.val j-z'.val j) := by ring
    rw [hsub,abs_mul,abs_of_pos (by positivity : 0<2/R.transverseWidth j)]
  · change dist ((2*z.val k.val-(R.lower k.val : ℝ)-(R.upper k.val : ℝ))/R.transverseWidth k.val)
      ((2*z'.val k.val-(R.lower k.val : ℝ)-(R.upper k.val : ℝ))/R.transverseWidth k.val)≤_
    rw [heq k.val hkj,dist_self]
    positivity

theorem point_eq_of_only_collapsed_coordinate (R : RectangularCell d) (j : Fin d)
    (hj : R.lower j=R.upper j) (z z' : CellClosedDomain R)
    (heq : ∀ k,k≠j → z.val k=z'.val k) : z=z' := by
  apply Subtype.ext
  funext k
  by_cases hkj : k=j
  · subst k
    have hz : z.val j=(R.lower j : ℝ) := le_antisymm
      (by simpa [hj] using (z.property j).2) (z.property j).1
    have hz' : z'.val j=(R.lower j : ℝ) := le_antisymm
      (by simpa [hj] using (z'.property j).2) (z'.property j).1
    exact hz.trans hz'.symm
  · exact heq k hkj

end RectangularCell

namespace PrismBoundaryData
variable {Z : Type*} [MetricSpace Z] {R : RectangularCell d} {i : Fin d}
variable {p q : Z} {S B D J : ℝ≥0} (F : PrismBoundaryData R i p q S B)
variable (H : ControlledContraction p D J)

theorem fill_first_dist_le (hi : R.lower i<R.upper i) (z z' : CellClosedDomain R)
    (heq : ∀ j,j≠i → z.val j=z'.val j) :
    dist (F.fill H hi z) (F.fill H hi z')≤
      (3*max S D : ℝ≥0)/R.transverseWidth i*|z.val i-z'.val i| := by
  unfold fill
  rw [R.normalizeTransverse_eq_of_except_first i z z' heq]
  have h := (H.coneValue_path_lipschitz F.pathFamily (R.normalizeTransverse i z')).dist_le_mul
    (R.firstIntervalParameter i hi z) (R.firstIntervalParameter i hi z')
  rw [R.firstIntervalParameter_dist i hi z z'] at h
  simpa only [div_mul_eq_mul_div,mul_div_assoc] using h

theorem fill_transverse_dist_le (hi : R.lower i<R.upper i) (j : Fin d)
    (hji : j≠i) (hj : R.lower j<R.upper j) (z z' : CellClosedDomain R)
    (heq : ∀ k,k≠j → z.val k=z'.val k) :
    dist (F.fill H hi z) (F.fill H hi z')≤
      2*(ControlledContraction.coneTransverseConstant S D J B : ℝ)/R.transverseWidth j*
        |z.val j-z'.val j| := by
  unfold fill
  rw [R.firstIntervalParameter_eq i hi z z' (heq i hji.symm)]
  have h := (H.coneValue_transverse_lipschitz F.pathFamily
    (R.firstIntervalParameter i hi z')).dist_le_mul (R.normalizeTransverse i z) (R.normalizeTransverse i z')
  calc
    _≤(ControlledContraction.coneTransverseConstant S D J B : ℝ)*
      dist (R.normalizeTransverse i z) (R.normalizeTransverse i z') := h
    _≤(ControlledContraction.coneTransverseConstant S D J B : ℝ)*
      ((2/R.transverseWidth j)*|z.val j-z'.val j|) := mul_le_mul_of_nonneg_left
        (R.normalizeTransverse_coordinate_dist_le i j hj z z' heq)
        (ControlledContraction.coneTransverseConstant S D J B).property
    _=_ := by ring

end PrismBoundaryData
end
end AbelianTargets


