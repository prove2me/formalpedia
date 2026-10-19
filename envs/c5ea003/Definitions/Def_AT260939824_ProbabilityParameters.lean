-- Prove2me | Definitions.Def_AT260939824_ProbabilityParameters
-- name    : AT260939824_ProbabilityParameters
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T03:25:38.681886+00:00
-- url     : https://prove2.me/theorems/0a70c095-c9de-42c6-8849-fd5a33d0ae28
-- title:
--   Affine coordinates on finite probability faces
-- statement:
--   Assign to each vertex $v$ of a finite set a parameter $c(v)\in[0,1]$. A distribution $p$ determines its affine parameter
--   $$\lambda_c(p)=\sum_v p(v)c(v)\in[0,1].$$
--   This parameter is continuous, evaluates to $c(v)$ on a point mass, respects convex mixtures, and has the prescribed constant value when all vertices in the positive support have that value.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Sections 2-7; https://arxiv.org/html/2609.39824v1. Formalization-specific infrastructure in the import closure of Theorem 1.4 and Proposition 7.1; individual helper assertions are not represented as separately numbered paper theorems. Original Lean module AbelianTargets/ProbabilityParameters.lean, selected declaration lines 11-18, 20-22, 24-28, 30-35, 37-45, 47-51; SHA-256 f8f1f8bc38f6fced3addd44bace423d506c5572f737c05e9ab8f4185a6f00e06. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_BottomEdgeSplice
import Definitions.Def_AT260939824_CarrierCellRealization
import Definitions.Def_AT260939824_CarrierFanMoves
import Definitions.Def_AT260939824_CarrierGeometry
import Definitions.Def_AT260939824_CompressedWords
import Definitions.Def_AT260939824_DigitPathRealization
import Definitions.Def_AT260939824_DoubleCoverLifts
import Definitions.Def_AT260939824_EndpointCorrection
import Definitions.Def_AT260939824_FixedSlotInterpolation
import Definitions.Def_AT260939824_IntervalCarriers
import Definitions.Def_AT260939824_Probability
import Definitions.Def_AT260939824_ProbabilityMap
import Definitions.Def_AT260939824_RectangleHalfGluing
import Definitions.Def_AT260939824_ReducedWalks
import Definitions.Def_AT260939824_RelativePathContraction
import Definitions.Def_AT260939824_Rounding
import Definitions.Def_AT260939824_SegmentedOddPath
import Definitions.Def_AT260939824_SupportGeometry
import Definitions.Def_AT260939824_SupportModel
import Definitions.Def_AT260939824_SupportPathClasses
import Definitions.Def_AT260939824_SupportWitness
import Definitions.Def_AT260939824_TopologicalWalks
import Definitions.Def_AT260939824_VariableRowFamilies
import Definitions.Def_AT260939824_WordPathHelpers
import Init
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Algebra.Group.Conj
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Ring.Parity
import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Int.Interval
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Chain
import Mathlib.Data.Nat.Log
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Constructions
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

/-! Affine unit-interval coordinates on literal probability faces. -/

namespace AbelianTargets.Probability
noncomputable section
open scoped BigOperators unitInterval
variable {V : Type*} [Fintype V]

def parameter (c : V → unitInterval) (p : Probability V) : unitInterval :=
  ⟨∑ v,p.mass v*(c v : ℝ),by
    constructor
    · exact Finset.sum_nonneg (fun v _ => mul_nonneg (p.nonneg v) (c v).property.1)
    · calc
        _ ≤ ∑ v,p.mass v*1 := Finset.sum_le_sum
          (fun v _ => mul_le_mul_of_nonneg_left (c v).property.2 (p.nonneg v))
        _ = 1 := by simpa using p.sum_one⟩

theorem continuous_parameter (c : V → unitInterval) : Continuous (parameter c) := by
  apply Continuous.subtype_mk
  exact continuous_finset_sum _ (fun v _ => (continuous_mass_apply v).mul continuous_const)

@[simp] theorem parameter_dirac (c : V → unitInterval) (v : V) :
    parameter c (dirac v)=c v := by
  classical
  apply Subtype.ext
  simp [parameter,dirac_mass]

theorem parameter_mix (c : V → unitInterval) (p q : Probability V) (r : unitInterval) :
    parameter c (mix p q r)=intervalMix (parameter c p) (parameter c q) r := by
  apply Subtype.ext
  change (∑ v,((1-(r : ℝ))*p.mass v+(r : ℝ)*q.mass v)*(c v : ℝ)) = _
  simp only [add_mul,mul_assoc,Finset.sum_add_distrib,← Finset.mul_sum]
  rfl

theorem parameter_eq_on_support {c d : V → unitInterval} (p : Probability V)
    (s : Set V) (hp : p.SupportedOn s) (h : ∀ v∈s,c v=d v) : parameter c p=parameter d p := by
  classical
  apply Subtype.ext
  apply Finset.sum_congr rfl
  intro v hv
  by_cases hs : v∈s
  · rw [h v hs]
  · simp [(supportedOn_iff_zero.mp hp) v hs]

theorem parameter_const (p : Probability V) (r : unitInterval) :
    parameter (fun _ => r) p=r := by
  apply Subtype.ext
  change (∑ v,p.mass v*(r : ℝ))=(r : ℝ)
  rw [← Finset.sum_mul,p.sum_one,one_mul]

end
end AbelianTargets.Probability


