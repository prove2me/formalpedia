-- Prove2me | Definitions.Def_AT260939824_AtlasBoundaryPathBounds
-- name    : AT260939824_AtlasBoundaryPathBounds
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T03:03:12.110264+00:00
-- url     : https://prove2.me/theorems/066cb1fe-0bc0-4c28-8f79-786dba256520
-- title:
--   Longitudinal bounds in prism boundary coordinates
-- statement:
--   Let $R$ be a rectangular cell with positive width $w_i=R_i^+-R_i^-$ in coordinate $i$. A fixed transverse boundary point determines a prism path with longitudinal coordinate $R_i^-+w_ir$, where $0\le r\le1$. If compatible lower-cell maps have coordinate bound $C$, the resulting boundary path has Lipschitz constant $Cw_i$.
--
--   This converts physical-coordinate bounds into the normalized path bounds used by relative extension.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (2026), Section(s) 5; https://arxiv.org/abs/2609.39824v1. This item is auxiliary infrastructure of the accompanying formalization, not a claim that each implementation definition is separately numbered in the paper. Original Lean module AbelianTargets/AtlasBoundaryPathBounds.lean, selected declaration lines 12-21, 23-39, 45-75; SHA-256 abc3ff96ddee1cad40b95a8fad11493ca9a42c15eeb778aaf8b9f08952c8c607. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_AnisotropicMarkers
import Definitions.Def_AT260939824_AtlasBoundaryCarrierMaps
import Definitions.Def_AT260939824_AtlasBoundaryCoordinateBounds
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

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-! The subdivided cell boundary retains its controlled first path variable. -/
namespace AbelianTargets
open scoped NNReal unitInterval
noncomputable section

theorem prismBoundaryPoint_first_update {d : ℕ} (R : RectangularCell d) (i : Fin d)
    (v : ConeSphere (R.ActiveTransverse i → ℝ)) (r : I) :
    (prismBoundaryPoint R i v r).val=Function.update (prismBoundaryPoint R i v 0).val i
      ((R.lower i : ℝ)+R.transverseWidth i*r) := by
  funext j
  by_cases hji : j=i
  · subst j
    simp [prismBoundaryPoint,RectangularCell.prismPoint,RectangularCell.prismCoordinates]
  · simp only [prismBoundaryPoint,RectangularCell.prismPoint,RectangularCell.prismCoordinates,
      dif_neg hji,Function.update_of_ne hji]

theorem prism_first_boundary_line {d : ℕ} (R : RectangularCell d) (i : Fin d)
    (hi : R.lower i<R.upper i) (v : ConeSphere (R.ActiveTransverse i → ℝ)) :
    ∀ s∈Set.Icc (R.lower i : ℝ) (R.upper i : ℝ),
      Function.update (prismBoundaryPoint R i v 0).val i s∈R.boundary := by
  intro s hs
  have hw : 0<R.transverseWidth i := sub_pos.mpr (by exact_mod_cast hi)
  let r : I := ⟨(s-(R.lower i : ℝ))/R.transverseWidth i,by
    constructor
    · exact div_nonneg (sub_nonneg.mpr hs.1) hw.le
    · apply (div_le_iff₀ hw).mpr
      dsimp [RectangularCell.transverseWidth]
      linarith [hs.2]⟩
  have he : (R.lower i : ℝ)+R.transverseWidth i*r=s := by
    dsimp [r]; field_simp; ring
  have hp := (prismBoundaryPoint R i v r).property
  rw [prismBoundaryPoint_first_update,he] at hp
  exact hp

namespace LowerCellCarrierMaps
variable {d : ℕ} {K₀ : Fin d → ℕ} {T : IntegerRectangularTiling d K₀}
variable {m K : ℕ} {i : Fin d} {R : RectangularCell d}

theorem prism_path_lipschitz (F : LowerCellCarrierMaps T m K i R) (hR : R∈T.cells)
    (hi : R.lower i<R.upper i) (C : ℝ≥0)
    (hcoord : ∀ (Q : RectangularCell d) (hQ : Q∈T.cells) (hrQ : Q.rank<R.rank)
      (w : RealCoordinates d) (x y : ℝ)
      (hx : Function.update w i x∈Q.closedBox) (hy : Function.update w i y∈Q.closedBox),
      dist (F.map Q hQ hrQ ⟨Function.update w i x,hx⟩)
        (F.map Q hQ hrQ ⟨Function.update w i y,hy⟩)≤C*|x-y|)
    (v : ConeSphere (R.ActiveTransverse i → ℝ)) :
    LipschitzWith (C*(R.transverseWidth i).toNNReal)
      (fun r : I => F.boundaryValue hR (prismBoundaryPoint R i v r)) := by
  have hw : 0<R.transverseWidth i := sub_pos.mpr (by exact_mod_cast hi)
  let z := (prismBoundaryPoint R i v 0).val
  have hline := prism_first_boundary_line R i hi v
  let x : I→ℝ := fun r => (R.lower i : ℝ)+R.transverseWidth i*r
  have hx : ∀ r : I,x r∈Set.Icc (R.lower i : ℝ) (R.upper i : ℝ) := by
    intro r
    have hr := (prismBoundaryPoint R i v r).property.1 i
    simpa only [prismBoundaryPoint,RectangularCell.prismPoint_first] using hr
  have hp : ∀ r : I,prismBoundaryPoint R i v r=⟨Function.update z i (x r),hline _ (hx r)⟩ := by
    intro r; apply Subtype.ext
    exact prismBoundaryPoint_first_update R i v r
  apply LipschitzWith.of_dist_le_mul
  intro r s
  have hh := F.boundary_coordinate_dist_le hR i C hcoord z hline (x r) (x s) (hx r) (hx s)
  rw [←hp r,←hp s] at hh
  have he : |x r-x s|=R.transverseWidth i*dist r s := by
    have he' : x r-x s=R.transverseWidth i*((r : ℝ)-(s : ℝ)) := by dsimp [x]; ring
    rw [he',abs_mul,abs_of_pos hw]
    rfl
  rw [he] at hh
  simpa only [NNReal.coe_mul,Real.coe_toNNReal _ hw.le,mul_assoc] using hh

end LowerCellCarrierMaps
end
end AbelianTargets


