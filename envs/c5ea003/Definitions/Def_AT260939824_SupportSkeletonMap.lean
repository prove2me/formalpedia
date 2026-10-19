-- Prove2me | Definitions.Def_AT260939824_SupportSkeletonMap
-- name    : AT260939824_SupportSkeletonMap
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T03:28:01.137991+00:00
-- url     : https://prove2.me/theorems/697f9fce-c512-4cd2-b481-41e9ac42eb95
-- title:
--   A support-pair formula on vertices and carrier edges
-- statement:
--   Let $p$ be a probability distribution on a finite vertex set labelled by carrier vertices $f(v)=(r_v,h_v)$. Its nonempty positive support has a least horizontal coordinate $r$. For support-torsion data with designated path $a$, define
--
--   $$S_f(p)=\operatorname{swap}^{r}\,a\!\left(\sum_{r_v>r}p(v)\right).$$
--
--   On a singleton face this is the parity-adjusted basepoint. On a vertical edge it is constant, and on a positive horizontal carrier edge it follows $a$ with parameter equal to the mass at the right endpoint. These face identities provide the skeleton formula used for gluing; no global continuity of the minimum-coordinate operation is assumed.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (2026), Section(s) 4, 7.1; https://arxiv.org/abs/2609.39824v1. This item is auxiliary infrastructure of the accompanying formalization; its implementation definitions are not asserted to be separately numbered in the paper. Original Lean module AbelianTargets/SupportSkeletonMap.lean, selected declaration lines 12-13, 15-24, 26-27, 29-33, 35-37, 39-47, 49-53, 61-64, 66-76, 78-93, 95-132; SHA-256 aa0680b97b649eafbc3388d5171202f2b25421959f4bd6f2fbb3dd8cd37b9f41. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

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
import Definitions.Def_AT260939824_ParitySwapGeometry
import Definitions.Def_AT260939824_Probability
import Definitions.Def_AT260939824_ProbabilityMap
import Definitions.Def_AT260939824_ProbabilityParameters
import Definitions.Def_AT260939824_ProbabilityTwoVertices
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

/-! A total support-space map whose restrictions to skeleton edges are literal paths. -/
namespace AbelianTargets
noncomputable section
open scoped unitInterval
attribute [local instance] Classical.propDecidable

namespace Probability
variable {V : Type*} [Fintype V]

def positiveCoordinates (f : V → ℤ) (p : Probability V) : Finset ℤ :=
  (Finset.univ.filter (fun v => 0<p.mass v)).image f

theorem positiveCoordinates_nonempty (f : V → ℤ) (p : Probability V) :
    (positiveCoordinates f p).Nonempty := by
  have hp : ∃v,0<p.mass v := by
    by_contra hn
    push_neg at hn
    have hz : ∀v,p.mass v=0 := fun v => le_antisymm (hn v) (p.nonneg v)
    have hs := p.sum_one
    simp [hz] at hs
  obtain ⟨v,hv⟩ := hp
  exact ⟨f v,Finset.mem_image.mpr ⟨v,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hv⟩,rfl⟩⟩

def minimumCoordinate (f : V → ℤ) (p : Probability V) : ℤ :=
  (positiveCoordinates f p).min' (positiveCoordinates_nonempty f p)

theorem minimumCoordinate_mem (f : V → ℤ) (p : Probability V) :
    ∃v,0<p.mass v ∧ f v=minimumCoordinate f p := by
  have h := Finset.min'_mem (positiveCoordinates f p) (positiveCoordinates_nonempty f p)
  obtain ⟨v,hv,he⟩ := Finset.mem_image.mp h
  exact ⟨v,(Finset.mem_filter.mp hv).2,he⟩

theorem minimumCoordinate_le (f : V → ℤ) (p : Probability V) (v : V) (hv : 0<p.mass v) :
    minimumCoordinate f p≤f v :=
  Finset.min'_le _ _ (Finset.mem_image.mpr ⟨v,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hv⟩,rfl⟩)

theorem minimumCoordinate_pair_left (f : V → ℤ) (p : Probability V) (u v : V)
    (hp : p.SupportedOn ({u,v} : Set V)) (hu : 0<p.mass u) (hord : f u≤f v) :
    minimumCoordinate f p=f u := by
  obtain ⟨w,hw,he⟩ := minimumCoordinate_mem f p
  have hs := hp w hw
  rcases hs with rfl | rfl
  · exact he.symm
  · have hm := minimumCoordinate_le f p u hu
    omega

theorem minimumCoordinate_singleton (f : V → ℤ) (p : Probability V) (v : V)
    (hp : p.SupportedOn ({v} : Set V)) : minimumCoordinate f p=f v := by
  obtain ⟨w,hw,he⟩ := minimumCoordinate_mem f p
  have hs : w=v := hp w hw
  simpa only [hs] using he.symm

end Probability

namespace SupportTorsionData
variable {W : Type*} [Fintype W] {H : SimpleGraph W} (D : SupportTorsionData H)
variable {V : Type*} [Fintype V]

def skeletonMap (f : V → IntervalCarriers.Vertex) (p : Probability V) : SupportPair H :=
  let r := p.minimumCoordinate (fun v => (f v).1)
  SupportPair.paritySwap H r (D.a (Probability.parameter
    (fun v => if r<(f v).1 then 1 else 0) p))

theorem skeletonMap_singleton (f : V → IntervalCarriers.Vertex) (p : Probability V) (v : V)
    (hp : p.SupportedOn ({v} : Set V)) :
    D.skeletonMap f p=SupportPair.paritySwap H (f v).1 D.base := by
  unfold skeletonMap
  rw [Probability.minimumCoordinate_singleton _ _ v hp]
  dsimp only
  have hz : Probability.parameter (fun w => if (f v).1<(f w).1 then (1:I) else 0) p=0 := by
    rw [Probability.parameter_eq_on_support p ({v}:Set V) hp
      (show ∀w∈({v}:Set V),(if (f v).1<(f w).1 then (1:I) else 0)=0 from by
        intro w hw; have : w=v := hw; subst w; simp),Probability.parameter_const]
  rw [hz,D.a.source]

theorem skeletonMap_vertical (f : V → IntervalCarriers.Vertex) (p : Probability V) (u v : V)
    (hp : p.SupportedOn ({u,v} : Set V)) (hcoord : (f u).1=(f v).1) :
    D.skeletonMap f p=SupportPair.paritySwap H (f u).1 D.base := by
  unfold skeletonMap
  have hr : p.minimumCoordinate (fun w => (f w).1)=(f u).1 := by
    obtain ⟨w,hw,he⟩ := Probability.minimumCoordinate_mem (fun w => (f w).1) p
    rcases hp w hw with rfl | rfl
    · exact he.symm
    · exact he.symm.trans hcoord.symm
  rw [hr]
  dsimp only
  have hz : Probability.parameter (fun w => if (f u).1<(f w).1 then (1:I) else 0) p=0 := by
    rw [Probability.parameter_eq_on_support p ({u,v}:Set V) hp
      (show ∀w∈({u,v}:Set V),(if (f u).1<(f w).1 then (1:I) else 0)=0 from by
        intro w hw; rcases hw with rfl | rfl <;> simp [hcoord]),Probability.parameter_const]
  rw [hz,D.a.source]

theorem skeletonMap_horizontal (f : V → IntervalCarriers.Vertex) (p : Probability V) (u v : V)
    (hp : p.SupportedOn ({u,v} : Set V))
    (hstep : IntervalCarriers.HorizontalStep (2*D.power+1) (f u) (f v)) :
    D.skeletonMap f p=SupportPair.paritySwap H (f u).1
      (D.a ⟨p.mass v,p.nonneg v,p.mass_le_one v⟩) := by
  have hcoord : (f u).1<(f v).1 := by
    have he := congrArg Prod.fst hstep
    have hpow : 0<((2*D.power+1:ℕ):ℤ)^(f u).2 := pow_pos (by positivity) _
    change (f v).1=(f u).1+((2*D.power+1:ℕ):ℤ)^(f u).2 at he
    omega
  have hne : u≠v := by intro he; subst v; exact (lt_irrefl _ hcoord)
  by_cases hu : 0<p.mass u
  · unfold skeletonMap
    rw [Probability.minimumCoordinate_pair_left _ _ u v hp hu (le_of_lt hcoord)]
    dsimp only
    have hparam : Probability.parameter (fun w => if (f u).1<(f w).1 then (1:I) else 0) p=
        ⟨p.mass v,p.nonneg v,p.mass_le_one v⟩ := by
      apply Subtype.ext
      change Probability.weightedCoordinate _ p=p.mass v
      rw [Probability.weightedCoordinate,p.weighted_pair_sum u v hne hp]
      simp [hcoord]
    rw [hparam]
  · have hzero : p.mass u=0 := le_antisymm (le_of_not_gt hu) (p.nonneg u)
    have hpv : p.SupportedOn ({v}:Set V) := by
      intro w hw
      rcases hp w hw with rfl | rfl
      · simp [hzero] at hw
      · rfl
    rw [D.skeletonMap_singleton f p v hpv]
    have hv : (⟨p.mass v,p.nonneg v,p.mass_le_one v⟩ : I)=1 := by
      apply Subtype.ext
      have hs := p.mass_pair_sum u v hne hp
      simpa [hzero] using hs
    rw [hv,D.a.target]
    have he := congrArg Prod.fst hstep
    change (f v).1=(f u).1+((2*D.power+1:ℕ):ℤ)^(f u).2 at he
    rw [he,SupportPair.paritySwap_odd_pow]
    by_cases hr : (f u).1%2=0 <;> simp [SupportPair.paritySwap,hr,SupportPair.swap_swap]

end SupportTorsionData
end
end AbelianTargets


