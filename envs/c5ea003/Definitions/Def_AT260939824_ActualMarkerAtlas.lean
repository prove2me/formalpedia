-- Prove2me | Definitions.Def_AT260939824_ActualMarkerAtlas
-- name    : AT260939824_ActualMarkerAtlas
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T02:53:42.849871+00:00
-- url     : https://prove2.me/theorems/06e705d8-71b7-4212-bd74-301b63a5f9df
-- title:
--   The rectangular atlas of retained marker boxes
-- statement:
--   Fix a lattice action, positive coordinate scales $L_i$, and continuous marker-box data with separation parameter $S\ge6$. At an action point $x$, the retained rectangles define an integer rectangular tiling whose coordinate widths are at most $6L_i$. Its atlas cells are the tiling's point-cell strata.
--
--   This interface connects concrete marker and cut data with the rectangular-cell domains used by the carrier-map construction.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (2026), Section(s) 3; https://arxiv.org/abs/2609.39824v1. This item is auxiliary infrastructure of the accompanying formalization, not a claim that each implementation definition is separately numbered in the paper. Original Lean module AbelianTargets/ActualMarkerAtlas.lean, selected declaration lines 14-22, 24-38, 40-44; SHA-256 ab7949a783bdd6f12436e0b78048b7d4c13021894eb248ebc80899eab5c93a95. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

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
import Definitions.Def_AT260939824_RetainedMarkerTiles
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
import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Separation.Profinite
import Mathlib.Topology.UniformSpace.HeineCantor

set_option autoImplicit false

/-! The actual bounded rectangular tiling, and its regular point-cell atlas,
constructed from continuous covariant marker cuts. -/

namespace AbelianTargets
noncomputable section

variable {d : ℕ} {L : Fin d → ℕ} {X : Type*}
variable [TopologicalSpace X] [AddAction (Lattice d) X] [ContinuousVAdd (Lattice d) X]
variable {M : AnisotropicClopenMarkers d L X} {S : ℕ}

theorem ContinuousMarkerBoxes.GridCell.bounded
    {B : ContinuousMarkerBoxes M S} {x : X} {a : Lattice d} {R : RectangularCell d}
    (hR : B.GridCell x a R) : R.HasBoundedSides (fun i => 6*L i) := by
  intro i
  have hb := B.cuts_bounds x a i
  have hr := (hR i).2
  change R.upper i-R.lower i ≤ ((6*L i : ℕ) : ℤ)
  push_cast
  omega

def ContinuousMarkerBoxes.tiling (B : ContinuousMarkerBoxes M S)
    (hL : ∀ i,1 ≤ L i) (hS : 6 ≤ S) (x : X) :
    IntegerRectangularTiling d (fun i => 6*L i) where
  tiles := B.retainedTiles x
  positive R hR i := by
    obtain ⟨a,ha,hR,hkeep⟩ := hR
    exact hR.positive i
  cover := B.retainedTiles_cover hL x
  interior_unique R hR Q hQ hz := by
    obtain ⟨a,hR⟩ := hR
    obtain ⟨b,hQ⟩ := hQ
    exact B.retained_interiors_unique hS x hR hQ hz
  bounded R hR := by
    obtain ⟨a,ha,hR,hkeep⟩ := hR
    exact hR.bounded

/-- The literal atlas at an action point: finite intersections of the minimal
faces of all incident retained marker rectangles. -/
def ContinuousMarkerBoxes.atlasCells (B : ContinuousMarkerBoxes M S)
    (hL : ∀ i,1 ≤ L i) (hS : 6 ≤ S) (x : X) : Set (RectangularCell d) :=
  (B.tiling hL hS x).cells









end
end AbelianTargets


