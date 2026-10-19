-- Prove2me | Theorems.Thm_AbelianTargets_RectangularCell_subcell_mem_dependencyUniverse
-- name    : AbelianTargets.RectangularCell.subcell_mem_dependencyUniverse
-- status  : Proved
-- author  : @username
-- created : 2026-10-19T03:48:15.587439+00:00
-- url     : https://prove2.me/theorems/cc1384ec-b3cf-41f5-8288-801360204aa1
-- title:
--   Every bounded subcell lies in a finite dependency universe
-- statement:
--   Fix a natural dimension $d$, coordinate bounds $K_i\in\mathbb N$, and a point $z\in\mathbb R^d$. Suppose an integer rectangular cell $R$ contains $z$ and has side width at most $K_i$ in each coordinate. If another integer cell $Q$ satisfies $\overline Q\subseteq\overline R$, then $Q$ belongs to the finite dependency universe at $z$ determined by the bounds $K$. In particular, both integer endpoints of $Q$ lie between $\lceil z_i-K_i\rceil$ and $\lfloor z_i+K_i\rfloor$.
--
--   Writing $Q^-_i,Q^+_i$ for the integer endpoints of $Q$, the finite bounds are
--   $$\lceil z_i-K_i\rceil\le Q^-_i\le Q^+_i\le\lfloor z_i+K_i\rfloor.$$
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (2026), Sections 3–6 and Proposition 7.1; https://arxiv.org/html/2609.39824v1. This helper is formalization-specific infrastructure, not a separately numbered assertion of the paper. Original Lean proof: AbelianTargets/FiniteAtlasDependencyPatterns.lean, lines 17–31; raw UTF-8 source SHA-256 ef0c547865ea892fde31bd569a4bf7556f61efa85fa8f5140f8a7f9b6431b255. No public source repository commit was available.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_AnisotropicMarkers
import Definitions.Def_AT260939824_AtlasBoxes
import Definitions.Def_AT260939824_ClopenMarkers
import Definitions.Def_AT260939824_ContinuousAtlasPatterns
import Definitions.Def_AT260939824_ContinuousMarkerBoxes
import Definitions.Def_AT260939824_CovariantCuts
import Definitions.Def_AT260939824_Dimension
import Definitions.Def_AT260939824_FiniteAtlasDependencyPatterns
import Definitions.Def_AT260939824_IntegerGridIntervals
import Definitions.Def_AT260939824_MarkerExistence
import Definitions.Def_AT260939824_MarkerMap
import Definitions.Def_AT260939824_MarkerPriorities
import Definitions.Def_AT260939824_MarkerWindows
import Definitions.Def_AT260939824_OrbitMarkerCuts
import Definitions.Def_AT260939824_ParityCoordinates
import Definitions.Def_AT260939824_ParityFields
import Definitions.Def_AT260939824_PriorityCuts
import Definitions.Def_AT260939824_Probability
import Definitions.Def_AT260939824_RectangularAtlasBoundary
import Definitions.Def_AT260939824_RectangularBoundaryStrata
import Definitions.Def_AT260939824_RectangularCells
import Definitions.Def_AT260939824_RectangularLocalFiniteness
import Definitions.Def_AT260939824_Rounding
import Definitions.Def_AT260939824_SupportModel
import Init
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Prod
import Mathlib.Data.Countable.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Preimage
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Interval
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Dynamics.Transitive
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Order.Filter.Finite
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Clopen
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.Constructions
import Mathlib.Topology.Instances.Discrete
import Mathlib.Topology.Instances.Int
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Separation.Profinite
import Mathlib.Topology.UniformSpace.HeineCantor

set_option autoImplicit false

/-! A finite atlas pattern containing every boundary dependency of every
cell through a fixed spatial point. The universe includes all subcells,
even when their boundary is far from the fixed point. -/
namespace AbelianTargets
end AbelianTargets
open AbelianTargets
open Filter Topology
namespace AbelianTargets.RectangularCell
end AbelianTargets.RectangularCell
open AbelianTargets
open AbelianTargets.RectangularCell
variable {d : ℕ}

theorem AbelianTargets.RectangularCell.subcell_mem_dependencyUniverse (K : Fin d→ℕ) (z : RealCoordinates d)
    (R Q : RectangularCell d) (hR : HasBoundedSides K R)
    (hz : z∈R.closedBox) (hsub : Q.closedBox⊆R.closedBox) :
    Q∈dependencyUniverse K z := by sorry
