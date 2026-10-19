-- Prove2me | Definitions.Def_AT260939824_FiniteAtlasDependencyPatterns
-- name    : AT260939824_FiniteAtlasDependencyPatterns
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T03:23:09.935976+00:00
-- url     : https://prove2.me/theorems/62d5d388-4f03-45f2-870e-b8c1cbec1711
-- title:
--   Finite cell patterns near a bounded atlas point
-- statement:
--   Let $K_j$ bound rectangular-cell widths in a tiling of $\mathbb R^d$, and fix a point $z$. The dependency universe is the finite set of integer rectangular cells whose lower and upper endpoints in coordinate $j$ lie between
--
--   $$\lceil z_j-K_j\rceil\quad\text{and}\quad\lfloor z_j+K_j\rfloor.$$
--
--   The dependency pattern of a particular tiling is the subset of this universe consisting of its actual cells. These finite geometric data are used to compare evaluations of atlas maps while retaining only bounded local information about the tiling.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (2026), Section(s) 3, 6; https://arxiv.org/abs/2609.39824v1. This item is auxiliary infrastructure of the accompanying formalization; its implementation definitions are not asserted to be separately numbered in the paper. Original Lean module AbelianTargets/FiniteAtlasDependencyPatterns.lean, selected declaration lines 13-15, 37-40; SHA-256 ef0c547865ea892fde31bd569a4bf7556f61efa85fa8f5140f8a7f9b6431b255. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_AnisotropicMarkers
import Definitions.Def_AT260939824_AtlasBoxes
import Definitions.Def_AT260939824_ClopenMarkers
import Definitions.Def_AT260939824_ContinuousAtlasPatterns
import Definitions.Def_AT260939824_ContinuousMarkerBoxes
import Definitions.Def_AT260939824_CovariantCuts
import Definitions.Def_AT260939824_Dimension
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
noncomputable section
open Filter Topology
namespace RectangularCell
variable {d : ℕ}

def dependencyUniverse (K : Fin d→ℕ) (z : RealCoordinates d) : Finset (RectangularCell d) :=
  (finite_bounded_endpoints (fun i=>Int.ceil (z i-(K i:ℝ)))
    (fun i=>Int.floor (z i+(K i:ℝ)))).toFinset



end RectangularCell
namespace IntegerRectangularTiling
variable {d : ℕ} {K : Fin d→ℕ}

def dependencyPattern (T : IntegerRectangularTiling d K) (z : RealCoordinates d) :
    Finset (RectangularCell d) := by
  classical
  exact (RectangularCell.dependencyUniverse K z).filter (fun R=>R∈T.cells)











end IntegerRectangularTiling
end
end AbelianTargets


