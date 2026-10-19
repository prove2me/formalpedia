-- Prove2me | Definitions.Def_AT260939824_IntegerPrismFilling
-- name    : AT260939824_IntegerPrismFilling
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T03:01:03.17964+00:00
-- url     : https://prove2.me/theorems/36791221-ff7a-4e1f-9eec-bcac2ccd0df0
-- title:
--   Relative filling of an integer rectangular prism
-- statement:
--   For a cell $R$ and a nondegenerate coordinate $i$, prism-boundary data consist of a continuous boundary map into a pseudometric space $Z$, fixed values $p,q$ on the two end faces, and prescribed path and transverse Lipschitz bounds. Given the required controlled contraction at $p$, the construction fills the closed prism continuously, agrees with the boundary map, and preserves the two endpoint values.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Sections 2-7; https://arxiv.org/html/2609.39824v1. Formalization-specific infrastructure in the import closure of Theorem 1.4 and Proposition 7.1; individual helper assertions are not represented as separately numbered paper theorems. Original Lean module AbelianTargets/IntegerPrismFilling.lean, selected declaration lines 11-13, 15-22, 24-31, 36-44, 46-55, 59-61, 63-66, 68-70, 72-74, 76-92, 94-95; SHA-256 84fdde154143d5fcb5eacf623798a69fd7d474f7caa43a9f2d800f17fc093056. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

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

/-! The actual relative cone filling on arbitrary integer rectangular
strata, including degenerate transverse coordinates. -/

namespace AbelianTargets
noncomputable section
open scoped unitInterval NNReal
variable {d : ℕ} {Z : Type*} [MetricSpace Z]

def prismBoundaryPoint (R : RectangularCell d) (i : Fin d)
    (v : ConeSphere (R.ActiveTransverse i → ℝ)) (r : unitInterval) : CellBoundaryDomain R :=
  ⟨(R.prismPoint i r ⟨v.val,v.property.le⟩).val,R.prismSphere_mem_boundary i r v⟩

theorem continuous_prismBoundaryPoint (R : RectangularCell d) (i : Fin d) :
    Continuous (fun z : ConeSphere (R.ActiveTransverse i → ℝ) × unitInterval =>
      prismBoundaryPoint R i z.1 z.2) := by
  apply Continuous.subtype_mk
  have hc : Continuous (fun v : ConeSphere (R.ActiveTransverse i → ℝ) =>
      (⟨v.val,v.property.le⟩ : ConeBall (R.ActiveTransverse i → ℝ))) := continuous_subtype_val.subtype_mk _
  exact continuous_subtype_val.comp ((R.continuous_prismPoint i).comp
    (continuous_snd.prodMk (hc.comp continuous_fst)))

structure PrismBoundaryData (R : RectangularCell d) (i : Fin d) (p q : Z) (S B : ℝ≥0) where
  map : C(CellBoundaryDomain R,Z)
  source : ∀ z : CellBoundaryDomain R,z.val i=(R.lower i : ℝ) → map z=p
  target : ∀ z : CellBoundaryDomain R,z.val i=(R.upper i : ℝ) → map z=q
  path_lipschitz : ∀ v : ConeSphere (R.ActiveTransverse i → ℝ),
    LipschitzWith S (fun r => map (prismBoundaryPoint R i v r))
  transverse : ∀ r : unitInterval,LipschitzWith B
    (fun v : ConeSphere (R.ActiveTransverse i → ℝ) => map (prismBoundaryPoint R i v r))

namespace PrismBoundaryData
variable {R : RectangularCell d} {i : Fin d} {p q : Z} {S B : ℝ≥0}

def path (F : PrismBoundaryData R i p q S B) (v : ConeSphere (R.ActiveTransverse i → ℝ)) : Path p q where
  toFun r := F.map (prismBoundaryPoint R i v r)
  continuous_toFun := F.map.continuous.comp ((continuous_prismBoundaryPoint R i).comp
    (continuous_const.prodMk continuous_id))
  source' := F.source _ (by simp [prismBoundaryPoint,R.prismPoint_first])
  target' := F.target _ (by
    change (R.prismPoint i 1 ⟨v.val,v.property.le⟩).val i=(R.upper i : ℝ)
    rw [R.prismPoint_first]
    simp [RectangularCell.transverseWidth])

def pathFamily (F : PrismBoundaryData R i p q S B) :
    ControlledContraction.BoundaryPathFamily (E := R.ActiveTransverse i → ℝ) p q S B where
  path := F.path
  path_lipschitz := F.path_lipschitz
  transverse := by
    apply LipschitzWith.of_dist_le_mul
    intro v w
    apply (ContinuousMap.dist_le (mul_nonneg B.property dist_nonneg)).mpr
    intro r
    exact (F.transverse r).dist_le_mul v w

variable {D J : ℝ≥0} (H : ControlledContraction p D J)

def fill (F : PrismBoundaryData R i p q S B) (hi : R.lower i < R.upper i)
    (z : CellClosedDomain R) : Z :=
  H.coneValue F.pathFamily (R.normalizeTransverse i z) (R.firstIntervalParameter i hi z)

theorem continuous_fill (F : PrismBoundaryData R i p q S B) (hi : R.lower i < R.upper i) :
    Continuous (F.fill H hi) :=
  (H.continuous_coneValue F.pathFamily).comp
    ((R.continuous_normalizeTransverse i).prodMk (R.continuous_firstIntervalParameter i hi))

theorem fill_source (F : PrismBoundaryData R i p q S B) (hi : R.lower i < R.upper i)
    (z : CellClosedDomain R) (hz : z.val i=(R.lower i : ℝ)) : F.fill H hi z=p := by
  rw [fill,R.firstIntervalParameter_zero i hi z hz,H.coneValue_source]

theorem fill_target (F : PrismBoundaryData R i p q S B) (hi : R.lower i < R.upper i)
    (z : CellClosedDomain R) (hz : z.val i=(R.upper i : ℝ)) : F.fill H hi z=q := by
  rw [fill,R.firstIntervalParameter_one i hi z hz,H.coneValue_target]

theorem fill_boundary (F : PrismBoundaryData R i p q S B) (hi : R.lower i < R.upper i)
    (z : CellBoundaryDomain R) : F.fill H hi ⟨z.val,z.property.1⟩=F.map z := by
  by_cases hlo : z.val i=(R.lower i : ℝ)
  · rw [F.fill_source H hi _ hlo,F.source z hlo]
  · by_cases hhi : z.val i=(R.upper i : ℝ)
    · rw [F.fill_target H hi _ hhi,F.target z hhi]
    · let v : ConeSphere (R.ActiveTransverse i → ℝ) :=
        ⟨(R.normalizeTransverse i ⟨z.val,z.property.1⟩).val,R.normalizeTransverse_boundary i z hlo hhi⟩
      let r := R.firstIntervalParameter i hi ⟨z.val,z.property.1⟩
      have he : prismBoundaryPoint R i v r=z := by
        apply Subtype.ext
        exact congrArg (fun w : CellClosedDomain R => w.val)
          (R.prismPoint_inverse i hi ⟨z.val,z.property.1⟩)
      change H.coneValue F.pathFamily ⟨v.val,by rw [v.property]⟩ r=F.map z
      rw [H.coneValue_boundary]
      change F.map (prismBoundaryPoint R i v r)=F.map z
      rw [he]

def continuousMap (F : PrismBoundaryData R i p q S B) (hi : R.lower i < R.upper i) :
    C(CellClosedDomain R,Z) := ⟨F.fill H hi,F.continuous_fill H hi⟩

end PrismBoundaryData
end
end AbelianTargets


