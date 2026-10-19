-- Prove2me | solution 1 for AbelianTargets.RectangularCell.subcell_mem_dependencyUniverse
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-19T04:08:17.027321+00:00
-- url     : https://prove2.me/submissions/e00a10dc-97b7-4a58-9040-5c6eb4dcc936

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_AnisotropicMarkers
import Definitions.Def_AT260939824_AtlasBoxes
import Definitions.Def_AT260939824_ClopenMarkers
import Definitions.Def_AT260939824_ContinuousAtlasPatterns
import Definitions.Def_AT260939824_ContinuousMarkerBoxes
import Definitions.Def_AT260939824_CovariantCuts
import Definitions.Def_AT260939824_Dimension
import Definitions.Def_AT260939824_FiniteAtlasDependencyPatterns
import Definitions.Def_AT260939824_FiniteRectangleIntersections
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

theorem solution (K : Fin d→ℕ) (z : RealCoordinates d)
    (R Q : RectangularCell d) (hR : HasBoundedSides K R)
    (hz : z∈R.closedBox) (hsub : Q.closedBox⊆R.closedBox) :
    Q∈dependencyUniverse K z := by
  rw [dependencyUniverse,Set.Finite.mem_toFinset]
  intro i
  have hs := (closedBox_subset_iff Q R).mp hsub i
  have hh := hz i
  have hd : (R.upper i:ℝ)-(R.lower i:ℝ)≤(K i:ℝ) := by exact_mod_cast hR i
  have hlo : z i-(K i:ℝ)≤(R.lower i:ℝ) := by linarith
  have hhi : (R.upper i:ℝ)≤z i+(K i:ℝ) := by linarith
  have ha : Int.ceil (z i-(K i:ℝ))≤R.lower i := Int.ceil_le.mpr hlo
  have hb : R.upper i≤Int.floor (z i+(K i:ℝ)) := Int.le_floor.mpr hhi
  exact ⟨ha.trans hs.1,(Q.ordered i).trans (hs.2.trans hb),
    (ha.trans hs.1).trans (Q.ordered i),hs.2.trans hb⟩
