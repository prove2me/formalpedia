-- Prove2me | Definitions.Def_AT260939824_ContinuousAtlasPatterns
-- name    : AT260939824_ContinuousAtlasPatterns
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T02:52:15.446176+00:00
-- url     : https://prove2.me/theorems/b98577a0-8891-4f37-855f-55e2757e2ddb
-- title:
--   Finite local cell patterns of a bounded rectangular tiling
-- statement:
--   Let $d\in\mathbb N$ and let $T$ be an integer rectangular tiling of $\mathbb R^d$ whose coordinate side lengths are bounded by $K_i\in\mathbb N$. For $z\in\mathbb R^d$, define its local cell pattern by
--   $$\mathcal P_T(z)=\{R\in\operatorname{Cells}(T):R\cap B_\infty(z,1)\ne\varnothing\}.$$
--   The pattern is a finite set: integer rectangles with the fixed side bounds that meet the unit maximum-metric ball have only finitely many possible endpoint vectors. The selected membership identity says precisely that $R\in\mathcal P_T(z)$ if and only if it is a tiling cell and its closed box meets that ball. This records the finite geometric data used by local atlas comparisons.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Sections 2–7, supporting construction for Theorem 1.4 and Proposition 7.1; https://arxiv.org/html/2609.39824v1. Formalization-specific infrastructure in the import closure; individual helper assertions are not represented as separately numbered paper theorems. Original Lean module AbelianTargets/ContinuousAtlasPatterns.lean, selected declaration lines 11-14, 16-25; SHA-256 d9d9f56e6a264a0c295029a5db0e784b98a340d5b6407522ba6aa32c2b52f24e. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_AnisotropicMarkers
import Definitions.Def_AT260939824_AtlasBoxes
import Definitions.Def_AT260939824_ClopenMarkers
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
import Definitions.Def_AbelianTargets260939824Actions
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

/-! Actual finite atlas patterns on a fixed spatial neighborhood. -/

namespace AbelianTargets
noncomputable section
open Filter Topology
namespace IntegerRectangularTiling
variable {d : ℕ} {K : Fin d → ℕ}

def localPattern (T : IntegerRectangularTiling d K) (z : RealCoordinates d) :
    Finset (RectangularCell d) := by
  classical
  exact (RectangularCell.finite_meeting_ball K z).toFinset.filter (fun R => R ∈ T.cells)

@[simp] theorem mem_localPattern (T : IntegerRectangularTiling d K)
    (z : RealCoordinates d) (R : RectangularCell d) :
    R ∈ T.localPattern z ↔ R ∈ T.cells ∧ (R.closedBox ∩ Metric.ball z 1).Nonempty := by
  classical
  simp only [localPattern,Finset.mem_filter,Set.Finite.mem_toFinset]
  constructor
  · rintro ⟨⟨hb,hi⟩,hR⟩
    exact ⟨hR,hi⟩
  · rintro ⟨hR,hi⟩
    exact ⟨⟨T.cells_bounded hR,hi⟩,hR⟩



end IntegerRectangularTiling

variable {d : ℕ} {L : Fin d → ℕ} {X : Type*}
variable [TopologicalSpace X] [AddAction (Lattice d) X] [ContinuousVAdd (Lattice d) X]
variable {M : AnisotropicClopenMarkers d L X} {S : ℕ}



end
end AbelianTargets


