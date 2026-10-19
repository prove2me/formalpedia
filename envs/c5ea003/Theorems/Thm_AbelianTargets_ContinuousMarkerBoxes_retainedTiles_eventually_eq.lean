-- Prove2me | Theorems.Thm_AbelianTargets_ContinuousMarkerBoxes_retainedTiles_eventually_eq
-- name    : AbelianTargets.ContinuousMarkerBoxes.retainedTiles_eventually_eq
-- status  : Proved
-- author  : @username
-- created : 2026-10-19T03:40:37.679988+00:00
-- url     : https://prove2.me/theorems/e228ed9a-7d7d-43cf-b6bf-40165ffc8b89
-- title:
--   Membership in a fixed retained marker tile is locally constant
-- statement:
--   Let $d,S\in\mathbb N$, $L:\{1,\ldots,d\}\to\mathbb N$, and let $\mathbb Z^d$ act continuously on a topological space $X$. Fix anisotropic clopen markers $M$ at scales $L$ and continuous marker-box data $B$: integer box cuts and finite priorities vary continuously, the cuts lie within three coordinate scales of their centers, and the prescribed marker separation and priority conditions hold. Subdivide each marker box using the cut levels of markers within six scales. Retain an elementary rectangle when its relative interior avoids every marker box of smaller priority. Write $\mathcal R_B(x)$ for the rectangles retained at $x$. For every integer rectangle $R$ and every $x\in X$, there is a neighborhood $U$ of $x$ such that
--   $$R\in\mathcal R_B(y)\ \Longleftrightarrow\ R\in\mathcal R_B(x)\qquad(y\in U).$$
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Sections 2–7, supporting construction for Proposition 7.1; https://arxiv.org/html/2609.39824v1. Formalization-specific helper: AbelianTargets/MarkerAtlasLocality.lean, lines 108–121; SHA256 216f0be2831f35a56dee13287d2a226279fafbbc94a6f5df15125b61bc14c787.

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
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Separation.Profinite
import Mathlib.Topology.UniformSpace.HeineCantor

set_option autoImplicit false

/-! Finite local cut inputs determine actual retained tiles. In particular
the retained status of every fixed parent/cell is locally constant. -/
namespace AbelianTargets
end AbelianTargets
open AbelianTargets
open Filter Topology
variable {d : ℕ} {L : Fin d → ℕ} {X : Type*}
variable [TopologicalSpace X] [AddAction (Lattice d) X] [ContinuousVAdd (Lattice d) X]
variable {M : AnisotropicClopenMarkers d L X} {S : ℕ}

theorem AbelianTargets.ContinuousMarkerBoxes.retainedTiles_eventually_eq
    (B : ContinuousMarkerBoxes M S) (R : RectangularCell d) (x : X) :
    ∀ᶠ y in 𝓝 x,R ∈ B.retainedTiles y ↔ R ∈ B.retainedTiles x := by sorry
