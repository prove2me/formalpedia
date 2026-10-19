-- Prove2me | Definitions.Def_AT260939824_AtlasBoundaryCarrierMaps
-- name    : AT260939824_AtlasBoundaryCarrierMaps
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T02:55:58.29783+00:00
-- url     : https://prove2.me/theorems/dad977c9-6223-43fc-87bc-9876846a4afb
-- title:
--   Compatible carrier maps on cell boundaries
-- statement:
--   Let $T$ be an integer rectangular tiling, let $i$ be a coordinate, and let $m,K$ be carrier parameters. A cell $R$ receives the interval carrier over $[R_i^-,R_i^+]$. Compatible continuous maps on lower-rank cells determine a continuous map on the boundary of $R$; carrier inclusions identify the values on shared subcells.
--
--   This supplies literal boundary data for extensions over an atlas cell, with no assumed global filling.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (2026), Section(s) 5; https://arxiv.org/abs/2609.39824v1. This item is auxiliary infrastructure of the accompanying formalization, not a claim that each implementation definition is separately numbered in the paper. Original Lean module AbelianTargets/AtlasBoundaryCarrierMaps.lean, selected declaration lines 14-18, 20-23, 29-32, 34-38, 40-42, 44-48, 50-57, 64-67, 69-82, 84-109, 111-112; SHA-256 8634211f5ec7c2f53ef708adc2a2a427963f3ddbe70705754bede3a7a2305d80. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_AnisotropicMarkers
import Definitions.Def_AT260939824_AtlasBoxes
import Definitions.Def_AT260939824_CarrierCellRealization
import Definitions.Def_AT260939824_CarrierGeometry
import Definitions.Def_AT260939824_CarrierIntervalInclusion
import Definitions.Def_AT260939824_ClopenMarkers
import Definitions.Def_AT260939824_CompressedWords
import Definitions.Def_AT260939824_ContinuousAtlasPatterns
import Definitions.Def_AT260939824_ContinuousMarkerBoxes
import Definitions.Def_AT260939824_CovariantCuts
import Definitions.Def_AT260939824_DigitPathRealization
import Definitions.Def_AT260939824_Dimension
import Definitions.Def_AT260939824_FiniteRectangleIntersections
import Definitions.Def_AT260939824_FixedSlotInterpolation
import Definitions.Def_AT260939824_IntegerGridIntervals
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

/-! Compatible maps on actual lower-rank strata lift continuously into
the literal carrier of a parent cell. The canonical value uses the true
point cell, and the finite closed boundary cover proves continuity. -/

namespace AbelianTargets
noncomputable section

namespace IntegerRectangularTiling
variable {d : ℕ} {K₀ : Fin d → ℕ} (T : IntegerRectangularTiling d K₀)

theorem pointCell_subset_cell {R : RectangularCell d} (hR : R ∈ T.cells)
    {z : RealCoordinates d} (hz : z ∈ R.closedBox) :
    (T.pointCell z).closedBox ⊆ R.closedBox := by
  obtain ⟨x,rfl⟩ := hR
  exact T.pointCell_closed_mono x z hz

theorem pointCell_rank_lt_cell_boundary {R : RectangularCell d} (hR : R ∈ T.cells)
    {z : RealCoordinates d} (hz : z ∈ R.boundary) : (T.pointCell z).rank < R.rank := by
  obtain ⟨x,rfl⟩ := hR
  exact T.pointCell_rank_lt_on_boundary x z hz

end IntegerRectangularTiling

variable {d : ℕ}

abbrev CellClosedDomain (R : RectangularCell d) := {z : RealCoordinates d // z ∈ R.closedBox}
abbrev CellBoundaryDomain (R : RectangularCell d) := {z : RealCoordinates d // z ∈ R.boundary}
abbrev CellIntervalCarrier (m K : ℕ) (i : Fin d) (R : RectangularCell d) :=
  IntervalCarriers.Realization m K (R.lower i) (R.upper i)

def cellIntervalInclude {m K : ℕ} (i : Fin d) {Q R : RectangularCell d}
    (hsub : Q.closedBox ⊆ R.closedBox) : CellIntervalCarrier m K i Q → CellIntervalCarrier m K i R :=
  IntervalCarriers.intervalInclusion
    ((RectangularCell.closedBox_subset_iff Q R).mp hsub i).1
    ((RectangularCell.closedBox_subset_iff Q R).mp hsub i).2

theorem cellIntervalInclude_isometry {m K : ℕ} (i : Fin d) {Q R : RectangularCell d}
    (hsub : Q.closedBox ⊆ R.closedBox) : Isometry (cellIntervalInclude (m := m) (K := K) i hsub) :=
  IntervalCarriers.intervalInclusion_isometry _ _

theorem cellIntervalInclude_comp {m K : ℕ} (i : Fin d) {P Q R : RectangularCell d}
    (hPQ : P.closedBox ⊆ Q.closedBox) (hQR : Q.closedBox ⊆ R.closedBox)
    (hPR : P.closedBox ⊆ R.closedBox) (p : CellIntervalCarrier m K i P) :
    cellIntervalInclude i hQR (cellIntervalInclude i hPQ p)=cellIntervalInclude i hPR p :=
  IntervalCarriers.intervalInclusion_comp _ _ _ _ p

structure LowerCellCarrierMaps {K₀ : Fin d → ℕ} (T : IntegerRectangularTiling d K₀)
    (m K : ℕ) (i : Fin d) (R : RectangularCell d) where
  map : ∀ Q : RectangularCell d,Q ∈ T.cells → Q.rank < R.rank →
    C(CellClosedDomain Q,CellIntervalCarrier m K i Q)
  compatible : ∀ (P Q : RectangularCell d) (hP : P ∈ T.cells) (hQ : Q ∈ T.cells)
    (hrP : P.rank < R.rank) (hrQ : Q.rank < R.rank) (hsub : P.closedBox ⊆ Q.closedBox)
    (z : CellClosedDomain P),
    cellIntervalInclude i hsub (map P hP hrP z)=map Q hQ hrQ ⟨z.val,hsub z.property⟩

namespace LowerCellCarrierMaps
variable {K₀ : Fin d → ℕ} {T : IntegerRectangularTiling d K₀}
variable {m K : ℕ} {i : Fin d} {R : RectangularCell d}
variable (F : LowerCellCarrierMaps T m K i R) (hR : R ∈ T.cells)

def boundaryValue (z : CellBoundaryDomain R) : CellIntervalCarrier m K i R :=
  cellIntervalInclude i (T.pointCell_subset_cell hR z.property.1)
    (F.map (T.pointCell z.val) ⟨z.val,rfl⟩ (T.pointCell_rank_lt_cell_boundary hR z.property)
      ⟨z.val,(T.pointCell z.val).relativeInterior_subset (T.mem_relativeInterior_pointCell z.val)⟩)

theorem boundaryValue_eq {Q : RectangularCell d} (hQ : Q ∈ T.cells)
    (hrQ : Q.rank < R.rank) (hQR : Q.closedBox ⊆ R.closedBox)
    (z : CellBoundaryDomain R) (hzQ : z.val ∈ Q.closedBox) :
    F.boundaryValue hR z=cellIntervalInclude i hQR (F.map Q hQ hrQ ⟨z.val,hzQ⟩) := by
  let P := T.pointCell z.val
  have hP : P ∈ T.cells := ⟨z.val,rfl⟩
  have hrP : P.rank < R.rank := T.pointCell_rank_lt_cell_boundary hR z.property
  have hPQ := T.pointCell_subset_cell hQ hzQ
  have hPR := T.pointCell_subset_cell hR z.property.1
  let zp : CellClosedDomain P :=
    ⟨z.val,P.relativeInterior_subset (T.mem_relativeInterior_pointCell z.val)⟩
  change cellIntervalInclude i hPR (F.map P hP hrP zp)=_
  rw [← cellIntervalInclude_comp i hPQ hQR hPR]
  rw [F.compatible P Q hP hQ hrP hrQ hPQ zp]

theorem continuous_boundaryValue : Continuous (F.boundaryValue hR) := by
  classical
  let J := {Q : RectangularCell d // Q ∈ T.boundaryCells R}
  letI : Fintype J := Fintype.ofFinset (T.boundaryCells R) (by simp)
  let A : J → Set (CellBoundaryDomain R) := fun Q => {z | z.val ∈ Q.val.closedBox}
  apply (locallyFinite_of_finite A).continuous
  · ext z
    simp only [Set.mem_univ,iff_true]
    have hP : T.pointCell z.val ∈ T.boundaryCells R := (T.mem_boundaryCells R _).mpr
      ⟨⟨z.val,rfl⟩,T.pointCell_subset_cell hR z.property.1,
        T.pointCell_rank_lt_cell_boundary hR z.property⟩
    exact Set.mem_iUnion.mpr ⟨⟨T.pointCell z.val,hP⟩,
      (T.pointCell z.val).relativeInterior_subset (T.mem_relativeInterior_pointCell z.val)⟩
  · intro Q
    exact Q.val.isClosed_closedBox.preimage continuous_subtype_val
  · intro Q
    obtain ⟨hQc,hQR,hrQ⟩ := (T.mem_boundaryCells R Q.val).mp Q.property
    apply continuousOn_iff_continuous_restrict.mpr
    let lift : {z : CellBoundaryDomain R // z ∈ A Q} → CellClosedDomain Q.val :=
      fun z => ⟨z.val.val,z.property⟩
    have hl : Continuous lift := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
    have hc := (cellIntervalInclude_isometry (m := m) (K := K) i hQR).continuous.comp
      ((F.map Q.val hQc hrQ).continuous.comp hl)
    convert hc using 1
    funext z
    exact F.boundaryValue_eq hR hQc hrQ hQR z.val z.property

def boundaryMap : C(CellBoundaryDomain R,CellIntervalCarrier m K i R) :=
  ⟨F.boundaryValue hR,F.continuous_boundaryValue hR⟩

end LowerCellCarrierMaps
end
end AbelianTargets


