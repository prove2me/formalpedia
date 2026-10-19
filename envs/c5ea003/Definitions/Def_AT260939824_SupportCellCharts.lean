-- Prove2me | Definitions.Def_AT260939824_SupportCellCharts
-- name    : AT260939824_SupportCellCharts
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T03:27:53.370989+00:00
-- url     : https://prove2.me/theorems/1ee97874-20bc-4961-bc48-39fba8af8784
-- title:
--   Support-space charts on presentation cells
-- statement:
--   Let $D$ be support torsion data for a finite graph $H$: paths $a:p\to\tau p$, $b=\tau a:\tau p\to p$, and a positive null power $(a*b)^k$. Put $m=2k+1$. On a presentation cell with origin $(r,h)$, assign height zero to its lower vertices and height one to its upper vertices; assign the lower vertex indexed by $n$ the alternating-path breakpoint $t_{k,n}$, and the upper left and right vertices the parameters zero and one. Averaging these two coordinates against a probability mass and evaluating the fixed relation homotopy defines a continuous raw cell chart. Its lower edges alternate between $a$ and $b$, its upper edge equals $a$, and its left and right vertical edges are constant at $p$ and $\tau p$, respectively. These explicit restrictions allow cell charts to glue.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Sections 2–7, supporting construction for Theorem 1.4 and Proposition 7.1; https://arxiv.org/html/2609.39824v1. Formalization-specific infrastructure in the import closure; individual helper assertions are not represented as separately numbered paper theorems. Original Lean module AbelianTargets/SupportCellCharts.lean, selected declaration lines 12-15, 17-22, 24-27, 29-34, 47-50, 52-53, 55-68, 70-82, 84-94, 96-107; SHA-256 8eae1f1ae71ee5920d578c6fea0659270641159fff8b2ff0638219cf63f78626. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

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

/-! A single continuous chart on each complete literal relation polygon. -/

namespace AbelianTargets
noncomputable section
open scoped unitInterval
attribute [local instance] Classical.propDecidable

namespace IntervalCarriers
def cellHeight (c v : Vertex) : I := if v.2=c.2+1 then 1 else 0
def cellTheta (k m : ℕ) (c v : Vertex) : I :=
  if v.2=c.2 then oddBreak k (((v.1-c.1)/(m : ℤ)^c.2).toNat)
  else if v.1=c.1 then 0 else 1

theorem cellHeight_lower (c : Vertex) (m n : ℕ) :
    cellHeight c (lowerVertex m c.1 c.2 n)=0 := by simp [cellHeight,lowerVertex]
theorem cellHeight_upperLeft (c : Vertex) : cellHeight c (upperLeft c.1 c.2)=1 := by
  simp [cellHeight,upperLeft]
theorem cellHeight_upperRight (c : Vertex) (m : ℕ) : cellHeight c (upperRight m c.1 c.2)=1 := by
  simp [cellHeight,upperRight]

theorem cellTheta_lower (k m : ℕ) (hm : 1≤m) (c : Vertex) (n : ℕ) :
    cellTheta k m c (lowerVertex m c.1 c.2 n)=oddBreak k n := by
  have hp : (m : ℤ)^c.2≠0 := pow_ne_zero _ (by exact_mod_cast (show m≠0 by omega))
  simp [cellTheta,lowerVertex,Int.mul_ediv_cancel _ hp]

theorem cellTheta_upperLeft (k m : ℕ) (c : Vertex) :
    cellTheta k m c (upperLeft c.1 c.2)=0 := by simp [cellTheta,upperLeft]
theorem cellTheta_upperRight (k m : ℕ) (hm : 1≤m) (c : Vertex) :
    cellTheta k m c (upperRight m c.1 c.2)=1 := by
  have hp : 0<(m : ℤ)^(c.2+1) := pow_pos (by exact_mod_cast (show 0<m by omega)) _
  simp [cellTheta,upperRight,show c.1+(m : ℤ)^(c.2+1)≠c.1 by omega]



end IntervalCarriers

namespace SupportTorsionData
variable {W : Type*} [Fintype W] {H : SimpleGraph W} (D : SupportTorsionData H)
variable {V : Type*} [Fintype V]

def rawCellChart (f : V → IntervalCarriers.Vertex) (c : IntervalCarriers.Vertex) :
    Probability V → SupportPair H :=
  D.affineChart (IntervalCarriers.cellHeight c ∘ f)
    (IntervalCarriers.cellTheta D.power (2*D.power+1) c ∘ f)

theorem continuous_rawCellChart (f : V → IntervalCarriers.Vertex) (c : IntervalCarriers.Vertex) :
    Continuous (D.rawCellChart f c) := D.continuous_affineChart _ _

theorem rawCellChart_lower_edge (f : V → IntervalCarriers.Vertex) (c : IntervalCarriers.Vertex)
    (n : ℕ) (hn : n<2*D.power+1) (l r : V)
    (hl : f l=IntervalCarriers.lowerVertex (2*D.power+1) c.1 c.2 n)
    (hr : f r=IntervalCarriers.lowerVertex (2*D.power+1) c.1 c.2 (n+1)) (t : I) :
    D.rawCellChart f c (Probability.mix (Probability.dirac l) (Probability.dirac r) t)=
      if n%2=0 then D.a t else D.b t := by
  unfold rawCellChart affineChart
  rw [Probability.parameter_mix,Probability.parameter_mix]
  simp only [Probability.parameter_dirac,Function.comp_apply,hl,hr,
    IntervalCarriers.cellHeight_lower,
    IntervalCarriers.cellTheta_lower D.power (2*D.power+1) (by omega)]
  have hz : intervalMix 0 0 t=0 := by apply Subtype.ext; simp [intervalMix]
  rw [hz,D.relationHomotopy.apply_zero]
  exact alternatingOddPath_on_slot D.a D.b D.power n hn t

theorem rawCellChart_upper_edge (f : V → IntervalCarriers.Vertex) (c : IntervalCarriers.Vertex)
    (u v : V) (hu : f u=IntervalCarriers.upperLeft c.1 c.2)
    (hv : f v=IntervalCarriers.upperRight (2*D.power+1) c.1 c.2) (t : I) :
    D.rawCellChart f c (Probability.mix (Probability.dirac u) (Probability.dirac v) t)=D.a t := by
  unfold rawCellChart affineChart
  rw [Probability.parameter_mix,Probability.parameter_mix]
  simp only [Probability.parameter_dirac,Function.comp_apply,hu,hv,
    IntervalCarriers.cellHeight_upperLeft,IntervalCarriers.cellHeight_upperRight,
    IntervalCarriers.cellTheta_upperLeft,
    IntervalCarriers.cellTheta_upperRight D.power (2*D.power+1) (by omega),intervalMix_zero_one]
  have ho : intervalMix 1 1 t=1 := by apply Subtype.ext; simp [intervalMix]
  rw [ho,D.relationHomotopy.apply_one]
  rfl

theorem rawCellChart_left_edge (f : V → IntervalCarriers.Vertex) (c : IntervalCarriers.Vertex)
    (l u : V) (hl : f l=IntervalCarriers.lowerVertex (2*D.power+1) c.1 c.2 0)
    (hu : f u=IntervalCarriers.upperLeft c.1 c.2) (t : I) :
    D.rawCellChart f c (Probability.mix (Probability.dirac l) (Probability.dirac u) t)=D.base := by
  unfold rawCellChart affineChart
  rw [Probability.parameter_mix,Probability.parameter_mix]
  simp only [Probability.parameter_dirac,Function.comp_apply,hl,hu,
    IntervalCarriers.cellTheta_lower D.power (2*D.power+1) (by omega),
    IntervalCarriers.cellTheta_upperLeft,oddBreak_zero]
  have hz : intervalMix 0 0 t=0 := by apply Subtype.ext; simp [intervalMix]
  rw [hz,D.relationHomotopy.source]

theorem rawCellChart_right_edge (f : V → IntervalCarriers.Vertex) (c : IntervalCarriers.Vertex)
    (l v : V) (hl : f l=IntervalCarriers.lowerVertex (2*D.power+1) c.1 c.2 (2*D.power+1))
    (hv : f v=IntervalCarriers.upperRight (2*D.power+1) c.1 c.2) (t : I) :
    D.rawCellChart f c (Probability.mix (Probability.dirac l) (Probability.dirac v) t)=
      SupportPair.swap H D.base := by
  unfold rawCellChart affineChart
  rw [Probability.parameter_mix,Probability.parameter_mix]
  simp only [Probability.parameter_dirac,Function.comp_apply,hl,hv,
    IntervalCarriers.cellTheta_lower D.power (2*D.power+1) (by omega),
    IntervalCarriers.cellTheta_upperRight D.power (2*D.power+1) (by omega),oddBreak_last]
  have ho : intervalMix 1 1 t=1 := by apply Subtype.ext; simp [intervalMix]
  rw [ho,D.relationHomotopy.target]

end SupportTorsionData
end
end AbelianTargets


