-- Prove2me | Definitions.Def_AT260939824_ParitySwapGeometry
-- name    : AT260939824_ParitySwapGeometry
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T03:26:49.376616+00:00
-- url     : https://prove2.me/theorems/63468d3c-7f6a-45a2-8e13-bdec275d60a5
-- title:
--   Parity powers of the support-shore swap
-- statement:
--   Let $H$ be a finite simple graph and let its support-pair space carry the involution exchanging its two probability shores. For any integer $r$, the parity action is the identity when $r$ is even and the shore swap when $r$ is odd. The bundle records continuity, compatibility with integer addition, and the coordinate identities used in lattice covariance.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Sections 2-7; https://arxiv.org/html/2609.39824v1. Formalization-specific infrastructure in the import closure of Theorem 1.4 and Proposition 7.1; individual helper assertions are not represented as separately numbered paper theorems. Original Lean module AbelianTargets/ParitySwapGeometry.lean, selected declaration lines 8-9, 11-15, 20-35, 37-46, 48-60; SHA-256 1f04bd3a6d7d8689afd6ec0744118a0a2e5f3e6621a8a39430b66bd0e6800020. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

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
import Definitions.Def_AT260939824_ProbabilityParameters
import Definitions.Def_AT260939824_RectangleHalfGluing
import Definitions.Def_AT260939824_ReducedWalks
import Definitions.Def_AT260939824_RelativePathContraction
import Definitions.Def_AT260939824_Rounding
import Definitions.Def_AT260939824_SegmentedOddPath
import Definitions.Def_AT260939824_SimplicialSupport
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
import Mathlib.Tactic.FieldSimp
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

/-! Literal parity covariance of the support-space shore swap. -/
namespace AbelianTargets.SupportPair
noncomputable section
variable {V : Type*} [Fintype V] (H : SimpleGraph V)

def paritySwap (r : ℤ) (z : SupportPair H) : SupportPair H :=
  if r%2=0 then z else swap H z

theorem continuous_paritySwap (r : ℤ) : Continuous (paritySwap H r) := by
  unfold paritySwap
  split_ifs
  · exact continuous_id
  · exact continuous_swap H



theorem paritySwap_add (r s : ℤ) (z : SupportPair H) :
    paritySwap H (r+s) z=paritySwap H r (paritySwap H s z) := by
  have hr₀ := Int.emod_nonneg r (by norm_num : (2:ℤ)≠0)
  have hr₁ := Int.emod_lt_of_pos r (by norm_num : (0:ℤ)<2)
  have hs₀ := Int.emod_nonneg s (by norm_num : (2:ℤ)≠0)
  have hs₁ := Int.emod_lt_of_pos s (by norm_num : (0:ℤ)<2)
  have he := Int.add_emod r s 2
  by_cases hr : r%2=0 <;> by_cases hs : s%2=0
  · have ha : (r+s)%2=0 := by omega
    simp [paritySwap,ha,hr,hs]
  · have ha : (r+s)%2≠0 := by omega
    simp [paritySwap,ha,hr,hs]
  · have ha : (r+s)%2≠0 := by omega
    simp [paritySwap,ha,hr,hs]
  · have ha : (r+s)%2=0 := by omega
    simp [paritySwap,ha,hr,hs,swap_swap]

theorem paritySwap_odd_pow (k j : ℕ) (r : ℤ) (z : SupportPair H) :
    paritySwap H (r+((2*k+1:ℕ):ℤ)^j) z=swap H (paritySwap H r z) := by
  have hb : ((2*k+1:ℕ):ℤ)%2=1 := by simp [Int.add_emod,Int.mul_emod]
  have hp : (((2*k+1:ℕ):ℤ)^j)%2=1 := by
    induction j with
    | zero => norm_num
    | succ j ih => rw [pow_succ,Int.mul_emod,ih,hb]; norm_num
  rw [paritySwap_add]
  simp only [paritySwap,hp,one_ne_zero,if_false]
  by_cases hr : r%2=0 <;> simp [hr,swap_swap]

theorem paritySwap_lower_coordinate (k j n : ℕ) (r : ℤ) (z : SupportPair H) :
    paritySwap H (r+(n:ℤ)*((2*k+1:ℕ):ℤ)^j) z=
      paritySwap H r (if n%2=0 then z else swap H z) := by
  have hb : ((2*k+1:ℕ):ℤ)%2=1 := by simp [Int.add_emod,Int.mul_emod]
  have hp : (((2*k+1:ℕ):ℤ)^j)%2=1 := by
    induction j with
    | zero => norm_num
    | succ j ih => rw [pow_succ,Int.mul_emod,ih,hb]; norm_num
  rw [paritySwap_add]
  have hn : ((n:ℤ)*((2*k+1:ℕ):ℤ)^j)%2=(n%2:ℕ) := by
    rw [Int.mul_emod,hp,mul_one,Int.emod_emod]
    exact (Int.natCast_mod n 2).symm
  simp only [paritySwap,hn,Nat.cast_eq_zero]

end
end AbelianTargets.SupportPair


