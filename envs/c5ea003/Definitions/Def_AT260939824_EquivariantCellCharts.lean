-- Prove2me | Definitions.Def_AT260939824_EquivariantCellCharts
-- name    : AT260939824_EquivariantCellCharts
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T03:28:40.807852+00:00
-- url     : https://prove2.me/theorems/662a1ad5-c54c-45e0-8e82-7d65213de551
-- title:
--   Parity-normalized charts on odd relation cells
-- statement:
--   Fix support-torsion data $D$ for a graph $H$, and let $m=2q+1$ be its odd carrier base. Given a vertex labelling $f$ and a relation-cell base vertex $c$, the equivariant cell chart applies the shore-swap involution according to the parity of $c$'s horizontal coordinate to the raw cell chart. It is continuous on the finite probability simplex.
--
--   On lower and upper horizontal boundary edges it follows the designated support-pair path, with parity determined by the starting horizontal coordinate. On vertical boundary edges it is constant at the appropriately swapped basepoint. The included vertex identities give the same parity formula at all vertices of the fan triangulation.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (2026), Section(s) 4, 7.1; https://arxiv.org/abs/2609.39824v1. This item is auxiliary infrastructure of the accompanying formalization; its implementation definitions are not asserted to be separately numbered in the paper. Original Lean module AbelianTargets/EquivariantCellCharts.lean, selected declaration lines 10-12, 14-16, 18-31, 33-40, 42-49, 51-61, 63-89, 91-98, 100-111; SHA-256 7ffd53a3ec4c379ff2169b67e7fbf0ee58eb17b6bd2757ce561b6e7d82fcee3a. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_BottomEdgeSplice
import Definitions.Def_AT260939824_CarrierCellRealization
import Definitions.Def_AT260939824_CarrierFanMoves
import Definitions.Def_AT260939824_CarrierGeometry
import Definitions.Def_AT260939824_CarrierTriangulation
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
import Definitions.Def_AT260939824_RectangleHalfGluing
import Definitions.Def_AT260939824_ReducedWalks
import Definitions.Def_AT260939824_RelativePathContraction
import Definitions.Def_AT260939824_Rounding
import Definitions.Def_AT260939824_SegmentedOddPath
import Definitions.Def_AT260939824_SimplicialSupport
import Definitions.Def_AT260939824_SupportCellCharts
import Definitions.Def_AT260939824_SupportGeometry
import Definitions.Def_AT260939824_SupportModel
import Definitions.Def_AT260939824_SupportPathClasses
import Definitions.Def_AT260939824_SupportRelationCharts
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

/-! Actual relation-polygon charts with the literal horizontal parity action. -/
namespace AbelianTargets.SupportTorsionData
noncomputable section
open scoped unitInterval
variable {W : Type*} [Fintype W] {H : SimpleGraph W} (D : SupportTorsionData H)
variable {V : Type*} [Fintype V]

def cellChart (f : V → IntervalCarriers.Vertex) (c : IntervalCarriers.Vertex)
    (p : Probability V) : SupportPair H :=
  SupportPair.paritySwap H c.1 (D.rawCellChart f c p)

theorem continuous_cellChart (f : V → IntervalCarriers.Vertex) (c : IntervalCarriers.Vertex) :
    Continuous (D.cellChart f c) :=
  (SupportPair.continuous_paritySwap H c.1).comp (D.continuous_rawCellChart f c)

theorem cellChart_lower_edge (f : V → IntervalCarriers.Vertex) (c : IntervalCarriers.Vertex)
    (n : ℕ) (hn : n<2*D.power+1) (l r : V)
    (hl : f l=IntervalCarriers.lowerVertex (2*D.power+1) c.1 c.2 n)
    (hr : f r=IntervalCarriers.lowerVertex (2*D.power+1) c.1 c.2 (n+1)) (t : I) :
    D.cellChart f c (Probability.mix (Probability.dirac l) (Probability.dirac r) t)=
      SupportPair.paritySwap H (f l).1 (D.a t) := by
  unfold cellChart
  rw [D.rawCellChart_lower_edge f c n hn l r hl hr]
  rw [hl]
  change _=SupportPair.paritySwap H (c.1+(n:ℤ)*((2*D.power+1:ℕ):ℤ)^c.2) (D.a t)
  rw [SupportPair.paritySwap_lower_coordinate]
  by_cases hn : n%2=0
  · simp [hn]
  · simp [hn,D.b_swap]

theorem cellChart_upper_edge (f : V → IntervalCarriers.Vertex) (c : IntervalCarriers.Vertex)
    (u v : V) (hu : f u=IntervalCarriers.upperLeft c.1 c.2)
    (hv : f v=IntervalCarriers.upperRight (2*D.power+1) c.1 c.2) (t : I) :
    D.cellChart f c (Probability.mix (Probability.dirac u) (Probability.dirac v) t)=
      SupportPair.paritySwap H (f u).1 (D.a t) := by
  unfold cellChart
  rw [D.rawCellChart_upper_edge f c u v hu hv,hu]
  rfl

theorem cellChart_left_edge (f : V → IntervalCarriers.Vertex) (c : IntervalCarriers.Vertex)
    (l u : V) (hl : f l=IntervalCarriers.lowerVertex (2*D.power+1) c.1 c.2 0)
    (hu : f u=IntervalCarriers.upperLeft c.1 c.2) (t : I) :
    D.cellChart f c (Probability.mix (Probability.dirac l) (Probability.dirac u) t)=
      SupportPair.paritySwap H (f l).1 D.base := by
  unfold cellChart
  rw [D.rawCellChart_left_edge f c l u hl hu,hl]
  simp [IntervalCarriers.lowerVertex]

theorem cellChart_right_edge (f : V → IntervalCarriers.Vertex) (c : IntervalCarriers.Vertex)
    (l v : V) (hl : f l=IntervalCarriers.lowerVertex (2*D.power+1) c.1 c.2 (2*D.power+1))
    (hv : f v=IntervalCarriers.upperRight (2*D.power+1) c.1 c.2) (t : I) :
    D.cellChart f c (Probability.mix (Probability.dirac l) (Probability.dirac v) t)=
      SupportPair.paritySwap H (f l).1 D.base := by
  unfold cellChart
  rw [D.rawCellChart_right_edge f c l v hl hv,hl]
  change SupportPair.paritySwap H c.1 (SupportPair.swap H D.base)=
    SupportPair.paritySwap H (c.1+((2*D.power+1:ℕ):ℤ)*((2*D.power+1:ℕ):ℤ)^c.2) D.base
  rw [mul_comm,←pow_succ,SupportPair.paritySwap_odd_pow]
  by_cases hr : c.1%2=0 <;> simp [SupportPair.paritySwap,hr,SupportPair.swap_swap]

theorem cellChart_lower_vertex (f : V → IntervalCarriers.Vertex) (c : IntervalCarriers.Vertex)
    (n : ℕ) (hn : n≤2*D.power+1) (l : V)
    (hl : f l=IntervalCarriers.lowerVertex (2*D.power+1) c.1 c.2 n) :
    D.cellChart f c (Probability.dirac l)=SupportPair.paritySwap H (f l).1 D.base := by
  unfold cellChart rawCellChart affineChart
  simp only [Probability.parameter_dirac,Function.comp_apply,hl,
    IntervalCarriers.cellHeight_lower,
    IntervalCarriers.cellTheta_lower D.power (2*D.power+1) (by omega)]
  rw [D.relationHomotopy.apply_zero]
  change SupportPair.paritySwap H c.1 ((alternatingOddPath D.a D.b D.power) (oddBreak D.power n))=
    SupportPair.paritySwap H (IntervalCarriers.lowerVertex (2*D.power+1) c.1 c.2 n).1 D.base
  by_cases hn' : n<2*D.power+1
  · have he := alternatingOddPath_on_slot D.a D.b D.power n hn' (0 : I)
    have hm : intervalMix (oddBreak D.power n) (oddBreak D.power (n+1)) 0=oddBreak D.power n := by
      apply Subtype.ext; simp [intervalMix]
    rw [hm] at he
    rw [he]
    simp only [Path.source]
    change _=SupportPair.paritySwap H (c.1+(n:ℤ)*((2*D.power+1:ℕ):ℤ)^c.2) D.base
    rw [SupportPair.paritySwap_lower_coordinate]
  · have he : n=2*D.power+1 := by omega
    subst n
    rw [oddBreak_last,(alternatingOddPath D.a D.b D.power).target]
    change SupportPair.paritySwap H c.1 (SupportPair.swap H D.base)=
      SupportPair.paritySwap H (c.1+((2*D.power+1:ℕ):ℤ)*((2*D.power+1:ℕ):ℤ)^c.2) D.base
    rw [mul_comm,←pow_succ,SupportPair.paritySwap_odd_pow]
    by_cases hr : c.1%2=0 <;> simp [SupportPair.paritySwap,hr,SupportPair.swap_swap]

theorem cellChart_upperLeft_vertex (f : V → IntervalCarriers.Vertex) (c : IntervalCarriers.Vertex)
    (u : V) (hu : f u=IntervalCarriers.upperLeft c.1 c.2) :
    D.cellChart f c (Probability.dirac u)=SupportPair.paritySwap H (f u).1 D.base := by
  unfold cellChart rawCellChart affineChart
  simp only [Probability.parameter_dirac,Function.comp_apply,hu,
    IntervalCarriers.cellHeight_upperLeft,IntervalCarriers.cellTheta_upperLeft,
    Path.Homotopy.source]
  rfl

theorem cellChart_upperRight_vertex (f : V → IntervalCarriers.Vertex) (c : IntervalCarriers.Vertex)
    (v : V) (hv : f v=IntervalCarriers.upperRight (2*D.power+1) c.1 c.2) :
    D.cellChart f c (Probability.dirac v)=SupportPair.paritySwap H (f v).1 D.base := by
  unfold cellChart rawCellChart affineChart
  simp only [Probability.parameter_dirac,Function.comp_apply,hv,
    IntervalCarriers.cellHeight_upperRight,
    IntervalCarriers.cellTheta_upperRight D.power (2*D.power+1) (by omega),
    Path.Homotopy.target]
  change SupportPair.paritySwap H c.1 (SupportPair.swap H D.base)=
    SupportPair.paritySwap H (c.1+((2*D.power+1:ℕ):ℤ)^(c.2+1)) D.base
  rw [SupportPair.paritySwap_odd_pow]
  by_cases hr : c.1%2=0 <;> simp [SupportPair.paritySwap,hr,SupportPair.swap_swap]

end
end AbelianTargets.SupportTorsionData


