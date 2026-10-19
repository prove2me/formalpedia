-- Prove2me | Definitions.Def_AT260939824_MarkerAtlasQuantitativeWidths
-- name    : AT260939824_MarkerAtlasQuantitativeWidths
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T03:01:12.86651+00:00
-- url     : https://prove2.me/theorems/5fe57fa3-e757-4041-a8e8-09f1c98c04d1
-- title:
--   Explicit lower and upper widths of marker-atlas cells
-- statement:
--   Let $B$ be continuous marker-box data with scales $L_j\ge1$ and separation parameter $S\ge24$. For every cell $R$ of its retained atlas and each coordinate $j$, write $w_j=R_j^+-R_j^-$. The included width estimates give
--
--   $$0<w_j\ \Longrightarrow\ \frac{L_j}{32(2S+1)^d}\le w_j,\qquad w_j\le6L_j.$$
--
--   A supporting integer-arithmetic lemma converts strict separation by $\lfloor L/(16P)\rfloor$ into a real lower width $L/(32P)$. Collapsed coordinates remain permitted; the positive lower bound is required only for coordinates whose two endpoints differ.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (2026), Section(s) 3, 5–6; https://arxiv.org/abs/2609.39824v1. This item is auxiliary infrastructure of the accompanying formalization; its implementation definitions are not asserted to be separately numbered in the paper. Original Lean module AbelianTargets/MarkerAtlasQuantitativeWidths.lean, selected declaration lines 8-27, 29-48; SHA-256 57603f005e7c507e61ecc1d91dd7dbf7fddec66561f3a5dbd2552f9acf2dd12b. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_ActualMarkerAtlas
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
import Definitions.Def_AT260939824_IntervalCarriers
import Definitions.Def_AT260939824_MarkerAtlasSideBounds
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
import Definitions.Def_AbelianTargets260939824Actions
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
open scoped NNReal

theorem integer_width_lower_from_cut_separation (L P : ℕ) (hP : 0<P) (A B : ℤ)
    (hAB : A<B) (hsep : ((L/(16*P) : ℕ) : ℤ)<B-A) :
    (L : ℝ≥0)/(32*(P : ℝ≥0))≤((B : ℝ)-(A : ℝ)).toNNReal := by
  let w := (B-A).toNat
  have hw : (w : ℤ)=B-A := Int.toNat_of_nonneg (by omega)
  have hnat : L/(16*P)<w := by exact_mod_cast (hw ▸ hsep)
  have hmul : L<16*P*w := by simpa only [Nat.mul_comm] using (@Nat.div_lt_iff_lt_mul (16*P) L w (by positivity)).mp hnat
  have hwreal : (w : ℝ)=(B : ℝ)-(A : ℝ) := by exact_mod_cast hw
  have hreal : (L : ℝ)<16*(P : ℝ)*((B : ℝ)-(A : ℝ)) := by
    have hh : (L : ℝ)<(16*P*w : ℕ) := by exact_mod_cast hmul
    simpa only [Nat.cast_mul,Nat.cast_ofNat,hwreal,mul_assoc] using hh
  have hwidth : 0<(B : ℝ)-(A : ℝ) := sub_pos.mpr (by exact_mod_cast hAB)
  have hp : 0<(P : ℝ) := by exact_mod_cast hP
  have hh : ((L : ℝ≥0)/(32*(P : ℝ≥0)) : ℝ)≤
      (((B : ℝ)-(A : ℝ)).toNNReal : ℝ) := by
    simp only [NNReal.coe_div,NNReal.coe_mul,NNReal.coe_ofNat,NNReal.coe_natCast,
      Real.coe_toNNReal _ hwidth.le]
    apply (div_le_iff₀ (by positivity : 0<(32 : ℝ)*(P : ℝ))).mpr
    nlinarith
  exact_mod_cast hh

theorem ContinuousMarkerBoxes.atlas_quantitative_widths
    {d : ℕ} {L : Fin d→ℕ} {X : Type*} [TopologicalSpace X]
    [AddAction (Lattice d) X] [ContinuousVAdd (Lattice d) X]
    {M : AnisotropicClopenMarkers d L X} {S : ℕ}
    (B : ContinuousMarkerBoxes M S) (hL : ∀i,1≤L i) (hS : 24≤S) (x : X)
    {R : RectangularCell d} (hR : R∈B.atlasCells hL (by omega) x) (j : Fin d) :
    (R.lower j<R.upper j → (L j : ℝ≥0)/(32*((2*S+1)^d : ℕ))≤(R.transverseWidth j).toNNReal) ∧
      (R.transverseWidth j).toNNReal≤6*(L j : ℝ≥0) := by
  constructor
  · intro hj
    have hb := B.atlas_side_bounds hL hS x hR j hj
    exact integer_width_lower_from_cut_separation (L j) ((2*S+1)^d) (by positivity) _ _ hj hb.1
  · have hb := (B.tiling hL (by omega) x).cells_bounded hR j
    have hw : 0≤R.transverseWidth j := sub_nonneg.mpr (by exact_mod_cast R.ordered j)
    have hh : ((R.transverseWidth j).toNNReal : ℝ)≤(6*(L j : ℝ≥0) : ℝ) := by
      rw [Real.coe_toNNReal _ hw]
      dsimp [RectangularCell.transverseWidth]
      have hbReal : ((R.upper j - R.lower j : ℤ) : ℝ)≤((6*L j : ℕ) : ℝ) := by exact_mod_cast hb
      simpa only [Int.cast_sub,Nat.cast_mul,Nat.cast_ofNat,NNReal.coe_mul,NNReal.coe_ofNat,NNReal.coe_natCast] using hbReal
    exact_mod_cast hh

end
end AbelianTargets


