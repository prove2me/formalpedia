-- Prove2me | Definitions.Def_AT260939824_SupportRelationCharts
-- name    : AT260939824_SupportRelationCharts
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T03:26:42.804378+00:00
-- url     : https://prove2.me/theorems/a0264d24-36b8-4fc4-9b58-9d1a25f2bd74
-- title:
--   A fixed relation homotopy and affine probability charts
-- statement:
--   Let $D$ be support torsion data for a finite graph $H$, with paths $a:p\to\tau p$, $b:\tau p\to p$, positive exponent $k$, and nullhomotopy of $(a*b)^k$. Choose a relative homotopy
--   $$F:I^2\to\mathcal S(H),\qquad F(0,t)=A_k(t),\quad F(1,t)=a(t),$$
--   where $A_k$ is the alternating path with $2k+1$ segments, and both endpoints remain fixed. For a finite vertex set $V$ and assigned parameters $h,\theta:V\to I$, define
--   $$\operatorname{Chart}_{h,\theta}(\mu)=F\left(\sum_v\mu(v)h(v),\sum_v\mu(v)\theta(v)\right).$$
--   The weighted averages lie in $I$, and the chart is continuous. This provides one fixed geometric chart for every relation cell with those vertex parameters.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Sections 2–7, supporting construction for Theorem 1.4 and Proposition 7.1; https://arxiv.org/html/2609.39824v1. Formalization-specific infrastructure in the import closure; individual helper assertions are not represented as separately numbered paper theorems. Original Lean module AbelianTargets/SupportRelationCharts.lean, selected declaration lines 13-14, 18-19, 21-24; SHA-256 ce9e5408ac653d27dd64b1c5e61fefd05e73f3a9e5129781bb919842ccb7ca64. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

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

/-! Explicit barycentric charts filling the odd Baumslag--Solitar relation. -/

namespace AbelianTargets
noncomputable section
open scoped unitInterval
attribute [local instance] Classical.propDecidable

namespace SupportTorsionData
variable {W : Type*} [Fintype W] {H : SimpleGraph W} (D : SupportTorsionData H)

def relationHomotopy : (alternatingOddPath D.a D.b D.power).Homotopy D.a :=
  Classical.choice D.alternating_odd_null

variable {V : Type*} [Fintype V]

def affineChart (height theta : V → I) (p : Probability V) : SupportPair H :=
  D.relationHomotopy (Probability.parameter height p,Probability.parameter theta p)

theorem continuous_affineChart (height theta : V → I) :
    Continuous (D.affineChart height theta) :=
  D.relationHomotopy.continuous.comp
    ((Probability.continuous_parameter height).prodMk (Probability.continuous_parameter theta))























end SupportTorsionData
end
end AbelianTargets


