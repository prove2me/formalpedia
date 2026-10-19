-- Prove2me | Definitions.Def_AT260939824_IntegerPrismTranslation
-- name    : AT260939824_IntegerPrismTranslation
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T03:19:11.200535+00:00
-- url     : https://prove2.me/theorems/645d5514-1ccd-4988-a7dc-46db4f300ae8
-- title:
--   Translation of active prism coordinates
-- statement:
--   Translating an integer cell $R$ by a lattice vector $a$ preserves the set of active transverse directions. This induces an isometric linear equivalence on their real coordinate spaces and maps between the corresponding cone balls and spheres. Closed-cell and boundary points translate by addition of $a$. These explicit transports identify the prism models used by translated atlas cells.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Sections 2-7; https://arxiv.org/html/2609.39824v1. Formalization-specific infrastructure in the import closure of Theorem 1.4 and Proposition 7.1; individual helper assertions are not represented as separately numbered paper theorems. Original Lean module AbelianTargets/IntegerPrismTranslation.lean, selected declaration lines 11-16, 18-20, 22-25, 27-30, 32-34, 36-38, 40-42, 68-70, 72-76; SHA-256 631dff3119d4b0fcc5727eda728506a7c6c1f74be2d6ef82fb579483a5f06fac. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

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

set_option backward.isDefEq.respectTransparency false

namespace AbelianTargets.RectangularCell
noncomputable section
open scoped unitInterval
variable {d : ℕ}

def activeTranslationEquiv (R : RectangularCell d) (a : Fin d→ℤ) (i : Fin d) :
    R.ActiveTransverse i ≃ (R.translate a).ActiveTransverse i where
  toFun j := ⟨j.val,j.property.1,by simpa [translate] using j.property.2⟩
  invFun j := ⟨j.val,j.property.1,by simpa [translate] using j.property.2⟩
  left_inv j := rfl
  right_inv j := rfl

def activeFunctionTranslation (R : RectangularCell d) (a : Fin d→ℤ) (i : Fin d) :
    (R.ActiveTransverse i→ℝ) ≃ᵢ ((R.translate a).ActiveTransverse i→ℝ) :=
  IsometryEquiv.piCongrLeft' (Y := fun _=>ℝ) (R.activeTranslationEquiv a i)

theorem activeFunctionTranslation_norm (R : RectangularCell d) (a : Fin d→ℤ) (i : Fin d)
    (v : R.ActiveTransverse i→ℝ) : ‖R.activeFunctionTranslation a i v‖=‖v‖ := by
  have hzero : R.activeFunctionTranslation a i 0=0 := rfl
  simpa only [hzero,dist_zero_right] using (R.activeFunctionTranslation a i).dist_eq v 0

def activeLinearTranslation (R : RectangularCell d) (a : Fin d→ℤ) (i : Fin d) :
    (R.ActiveTransverse i→ℝ) ≃ₗᵢ[ℝ] ((R.translate a).ActiveTransverse i→ℝ) where
  toLinearEquiv := LinearEquiv.piCongrLeft' ℝ (fun _=>ℝ) (R.activeTranslationEquiv a i)
  norm_map' v := R.activeFunctionTranslation_norm a i v

def translateConeBall (R : RectangularCell d) (a : Fin d→ℤ) (i : Fin d)
    (v : ConeBall (R.ActiveTransverse i→ℝ)) : ConeBall ((R.translate a).ActiveTransverse i→ℝ) :=
  ⟨R.activeFunctionTranslation a i v.val,by rw [R.activeFunctionTranslation_norm];exact v.property⟩

def translateConeSphere (R : RectangularCell d) (a : Fin d→ℤ) (i : Fin d)
    (v : ConeSphere (R.ActiveTransverse i→ℝ)) : ConeSphere ((R.translate a).ActiveTransverse i→ℝ) :=
  ⟨R.activeFunctionTranslation a i v.val,by rw [R.activeFunctionTranslation_norm];exact v.property⟩

@[simp] theorem transverseWidth_translate (R : RectangularCell d) (a : Fin d→ℤ) (j : Fin d) :
    (R.translate a).transverseWidth j=R.transverseWidth j := by
  simp [transverseWidth,translate]



def translateClosedPoint (R : RectangularCell d) (a : Fin d→ℤ) (z : CellClosedDomain R) :
    CellClosedDomain (R.translate a) :=
  ⟨translateCoordinates a z.val,(R.mem_closedBox_translateCoordinates a z.val).mpr z.property⟩

def translateBoundaryPoint (R : RectangularCell d) (a : Fin d→ℤ) (z : CellBoundaryDomain R) :
    CellBoundaryDomain (R.translate a) :=
  ⟨translateCoordinates a z.val,
    (R.mem_closedBox_translateCoordinates a z.val).mpr z.property.1,
    fun h => z.property.2 ((R.mem_relativeInterior_translate a z.val).mp h)⟩







end
end AbelianTargets.RectangularCell


