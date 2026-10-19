-- Prove2me | Definitions.Def_AT260939824_ConeDomainNaturality
-- name    : AT260939824_ConeDomainNaturality
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T03:19:33.942501+00:00
-- url     : https://prove2.me/theorems/fcb71b76-f1b3-43b0-a9cc-63f4524671dd
-- title:
--   Unit-ball and sphere maps induced by linear isometries
-- statement:
--   Let $E,F$ be real normed vector spaces and let $k:E\to F$ be a linear isometric equivalence. It induces maps between their closed unit balls and between their unit spheres by restriction:
--
--   $$ x\longmapsto k(x). $$
--
--   Norm preservation supplies the membership witnesses. These domain maps let cone constructions be compared under changes of the transverse coordinate space.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (2026), Section(s) 5; https://arxiv.org/abs/2609.39824v1. This item is auxiliary infrastructure of the accompanying formalization, not a claim that each implementation definition is separately numbered in the paper. Original Lean module AbelianTargets/ConeDomainNaturality.lean, selected declaration lines 14-15, 17-18, 25-27; SHA-256 75529b86ab8ae4b7227faef94b711bd771519611bb4743a3cf1f8ec1379aaf60. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_CarrierCellRealization
import Definitions.Def_AT260939824_CarrierGeometry
import Definitions.Def_AT260939824_CompressedWords
import Definitions.Def_AT260939824_ControlledCone
import Definitions.Def_AT260939824_DigitPathRealization
import Definitions.Def_AT260939824_FixedSlotInterpolation
import Definitions.Def_AT260939824_IntervalCarriers
import Definitions.Def_AT260939824_Probability
import Definitions.Def_AT260939824_ProbabilityMap
import Definitions.Def_AT260939824_RelativeContractionNaturality
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
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Analysis.Normed.Operator.LinearIsometry
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
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Constructions
import Mathlib.Topology.ContinuousMap.Compact
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

/-! The relative cone formula respects linear isometries of the transverse
coordinate space. In particular, a relabeling of active rectangular axes
does not change the filling. -/

namespace AbelianTargets
open scoped unitInterval NNReal
noncomputable section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def coneBallMap (k : E ≃ₗᵢ[ℝ] F) (x : ConeBall E) : ConeBall F :=
  ⟨k x.val,by simpa using x.property⟩

def coneSphereMap (k : E ≃ₗᵢ[ℝ] F) (x : ConeSphere E) : ConeSphere F :=
  ⟨k x.val,by simpa using x.property⟩



@[simp] theorem coneParameter_linearIsometry (k : E ≃ₗᵢ[ℝ] F) (x : ConeBall E) :
    coneParameter (coneBallMap k x)=coneParameter x := by
  simp [coneParameter,coneBallMap]

namespace ControlledContraction
variable {Z : Type*} [MetricSpace Z] {p q : Z} {D J S B : ℝ≥0}
variable (H : ControlledContraction p D J)





end ControlledContraction
end
end AbelianTargets


