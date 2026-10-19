-- Prove2me | Theorems.Thm_AbelianTargets_IntervalCarriers_CarrierProjectionCharts_eval_eq_cell
-- name    : AbelianTargets.IntervalCarriers.CarrierProjectionCharts.eval_eq_cell
-- status  : Proved
-- author  : @username
-- created : 2026-10-19T03:37:33.668848+00:00
-- url     : https://prove2.me/theorems/957f8dcc-564f-4543-89cb-06af6bbd8a75
-- title:
--   The glued projection agrees with each cell chart
-- statement:
--   Let $m\ge1$, let $K$ be a natural height, and let $A,B$ be integer horizontal bounds. Suppose $D$ is a compatible family of carrier projection charts with target a topological space $Z$. If a realization point $p$ has positive support inside a fan triangle of a carrier cell $c$, then its global evaluation equals that cell chart:
--   $$D.\mathrm{eval}(p)=D.\mathrm{cell}_c(p).$$
--   This agreement holds even when the definition of the global evaluation selects a different incident cell.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (2026), Sections 3–6 and Proposition 7.1; https://arxiv.org/html/2609.39824v1. This helper is formalization-specific infrastructure, not a separately numbered assertion of the paper. Original Lean proof: AbelianTargets/CarrierProjectionGluing.lean, lines 149–169; raw UTF-8 source SHA-256 6292cc79a9be79a98223cbfc53b15537731222a3d3d6f329b428789046a0d5aa. No public source repository commit was available.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_CarrierCellRealization
import Definitions.Def_AT260939824_CarrierGeometry
import Definitions.Def_AT260939824_CarrierProjectionGluing
import Definitions.Def_AT260939824_CompressedWords
import Definitions.Def_AT260939824_DigitPathRealization
import Definitions.Def_AT260939824_FixedSlotInterpolation
import Definitions.Def_AT260939824_IntervalCarriers
import Definitions.Def_AT260939824_Probability
import Definitions.Def_AT260939824_RelativePathContraction
import Definitions.Def_AT260939824_Rounding
import Definitions.Def_AT260939824_SimplicialChartGluing
import Definitions.Def_AT260939824_SimplicialSupport
import Definitions.Def_AT260939824_SupportGeometry
import Definitions.Def_AT260939824_SupportModel
import Definitions.Def_AT260939824_TriangleChartIntersections
import Init
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Algebra.Group.Conj
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Analysis.Normed.Module.RCLike.Real
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
import Mathlib.Topology.Homotopy.Path
import Mathlib.Topology.Instances.Real.Lemmas
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
/-! Global carrier projections assembled from polygon and skeleton charts. -/
namespace AbelianTargets.IntervalCarriers
end AbelianTargets.IntervalCarriers
open AbelianTargets
open AbelianTargets.IntervalCarriers
attribute [local instance] Classical.propDecidable
namespace AbelianTargets.IntervalCarriers.CarrierProjectionCharts
end AbelianTargets.IntervalCarriers.CarrierProjectionCharts
open AbelianTargets
open AbelianTargets.IntervalCarriers
open AbelianTargets.IntervalCarriers.CarrierProjectionCharts
variable {m K : ℕ} {A B : ℤ} {Z : Type*} [TopologicalSpace Z]

theorem AbelianTargets.IntervalCarriers.CarrierProjectionCharts.eval_eq_cell (D : CarrierProjectionCharts m K A B Z) (hm : 1≤m)
    (p : Realization m K A B) (c : Vertex) (hc : c∈carrierCells m K A B)
    (t : Finset Vertex) (ht : IsFanTriangle m c t) (hp : RawSupported p.1 t) :
    D.eval hm p=D.cell c p.1 := by sorry
