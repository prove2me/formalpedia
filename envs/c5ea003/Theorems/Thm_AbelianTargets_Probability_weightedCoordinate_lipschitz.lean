-- Prove2me | Theorems.Thm_AbelianTargets_Probability_weightedCoordinate_lipschitz
-- name    : AbelianTargets.Probability.weightedCoordinate_lipschitz
-- status  : Proved
-- author  : @username
-- created : 2026-10-19T03:42:27.239977+00:00
-- url     : https://prove2.me/theorems/1897e802-31f9-4296-a3ee-b904d1e68a42
-- title:
--   Lipschitz bound for a weighted probability coordinate
-- statement:
--   Let $V$ be a finite set and $c:V\to\mathbb R$ arbitrary. Equip the probability simplex $\Delta(V)$ with the supremum distance on its mass coordinates. The weighted coordinate
--   $$
--   W_c(p)=\sum_{v\in V}p(v)c(v)
--   $$
--   is Lipschitz with constant
--   $$
--   K_c=\sum_{v\in V}|c(v)|.
--   $$
--   Equivalently, for all probability distributions $p,q$,
--   $$
--   |W_c(p)-W_c(q)|\le K_c\,d_\infty(p,q).
--   $$
--   The coefficients may have either sign, and no nonemptiness assumption on $V$ is imposed.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Sections 2.5 and 4, barycentric carrier coordinates supporting Lemma 4.1; https://arxiv.org/html/2609.39824v1#S4. Auxiliary formalization result in original module AbelianTargets/ProbabilityTwoVertices.lean, authoritative declaration span lines 16-30, SHA-256 b519bc40567569c7d4afc3111657083941f20b383c0e75e0590b1a9d4542eaf9. Frozen original source is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_CarrierCellRealization
import Definitions.Def_AT260939824_CarrierGeometry
import Definitions.Def_AT260939824_CompressedWords
import Definitions.Def_AT260939824_DigitPathRealization
import Definitions.Def_AT260939824_FixedSlotInterpolation
import Definitions.Def_AT260939824_IntervalCarriers
import Definitions.Def_AT260939824_Probability
import Definitions.Def_AT260939824_ProbabilityTwoVertices
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

/-! Exact barycentric coordinates on an edge, used to invert the literal
height-zero carrier parametrization. -/
namespace AbelianTargets.Probability
end AbelianTargets.Probability
open AbelianTargets
open AbelianTargets.Probability
open scoped BigOperators unitInterval NNReal
variable {V : Type*} [Fintype V]

theorem AbelianTargets.Probability.weightedCoordinate_lipschitz (c : V → ℝ) :
    LipschitzWith (weightedCoordinateConstant c) (weightedCoordinate c) := by sorry
