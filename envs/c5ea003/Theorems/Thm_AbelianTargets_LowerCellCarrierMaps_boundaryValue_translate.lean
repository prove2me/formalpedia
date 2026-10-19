-- Prove2me | Theorems.Thm_AbelianTargets_LowerCellCarrierMaps_boundaryValue_translate
-- name    : AbelianTargets.LowerCellCarrierMaps.boundaryValue_translate
-- status  : Proved
-- author  : @username
-- created : 2026-10-19T03:39:39.810007+00:00
-- url     : https://prove2.me/theorems/b029232d-6afb-4d40-b60e-fbc89a442549
-- title:
--   Compatible lower-cell carrier maps give translation-equivariant boundary values
-- statement:
--   Let $T$ be an integer rectangular tiling in dimension $d$ with its specified local-finiteness bounds, let $R$ be one of its cells, fix natural carrier parameters $m,K$ and a coordinate $i$, and let $a\in\mathbb Z^d$. Suppose $F$ assigns continuous maps from closed cells of rank less than $\operatorname{rank}R$ into the height-$K$ interval carrier over their $i$th coordinate interval, compatibly with cell inclusions. Let $G$ be such a family for $T+a$ below $R+a$. Assume that for every such cell $Q$ and point $z\in Q$,
--   $$G_{Q+a}(z+a)=T_{a_i}(F_Q(z)),$$
--   where $T_{a_i}$ translates carrier vertices horizontally. The glued boundary values then satisfy
--   $$G_{\partial(R+a)}(z+a)=T_{a_i}(F_{\partial R}(z))\qquad(z\in\partial R),$$
--   with $\partial R$ denoting the relative boundary.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Sections 2–7, supporting construction for Proposition 7.1; https://arxiv.org/html/2609.39824v1. Formalization-specific helper: AbelianTargets/AtlasBoundaryTranslation.lean, lines 61–86; SHA256 3219bccd23e71e915838e2d52d7e9c4a931e9d4c25892af90f81b3143b1fc5e9.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_AnisotropicMarkers
import Definitions.Def_AT260939824_AtlasBoundaryCarrierMaps
import Definitions.Def_AT260939824_AtlasBoundaryTranslation
import Definitions.Def_AT260939824_AtlasBoxes
import Definitions.Def_AT260939824_AtlasRankRecursion
import Definitions.Def_AT260939824_CarrierCellRealization
import Definitions.Def_AT260939824_CarrierGeometry
import Definitions.Def_AT260939824_CarrierIntervalInclusion
import Definitions.Def_AT260939824_ClopenMarkers
import Definitions.Def_AT260939824_CompressedWords
import Definitions.Def_AT260939824_ConeDomainNaturality
import Definitions.Def_AT260939824_ContinuousAtlasPatterns
import Definitions.Def_AT260939824_ContinuousMarkerBoxes
import Definitions.Def_AT260939824_ControlledCone
import Definitions.Def_AT260939824_CovariantCuts
import Definitions.Def_AT260939824_DigitPathRealization
import Definitions.Def_AT260939824_Dimension
import Definitions.Def_AT260939824_FixedSlotInterpolation
import Definitions.Def_AT260939824_IntegerGridIntervals
import Definitions.Def_AT260939824_IntegerPrismChart
import Definitions.Def_AT260939824_IntegerPrismFilling
import Definitions.Def_AT260939824_IntegerPrismTranslation
import Definitions.Def_AT260939824_IntervalCarriers
import Definitions.Def_AT260939824_MarkerExistence
import Definitions.Def_AT260939824_MarkerMap
import Definitions.Def_AT260939824_MarkerPriorities
import Definitions.Def_AT260939824_MarkerWindows
import Definitions.Def_AT260939824_OrbitMarkerCuts
import Definitions.Def_AT260939824_ParityCoordinates
import Definitions.Def_AT260939824_ParityFields
import Definitions.Def_AT260939824_PriorityCuts
import Definitions.Def_AT260939824_Probability
import Definitions.Def_AT260939824_ProbabilityMap
import Definitions.Def_AT260939824_ProbabilityPushDirac
import Definitions.Def_AT260939824_RectangularAtlasBoundary
import Definitions.Def_AT260939824_RectangularBoundaryStrata
import Definitions.Def_AT260939824_RectangularCells
import Definitions.Def_AT260939824_RectangularCone
import Definitions.Def_AT260939824_RectangularTranslation
import Definitions.Def_AT260939824_RegularAnisotropicAtlas
import Definitions.Def_AT260939824_RelativeContractionNaturality
import Definitions.Def_AT260939824_RelativePathContraction
import Definitions.Def_AT260939824_Rounding
import Definitions.Def_AT260939824_SupportGeometry
import Definitions.Def_AT260939824_SupportModel
import Init
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Algebra.Group.Conj
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Prod
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
import Mathlib.Data.Countable.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Preimage
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Interval
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Dynamics.Transitive
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Order.Filter.Finite
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Clopen
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.Constructions
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Homotopy.Path
import Mathlib.Topology.Instances.Discrete
import Mathlib.Topology.Instances.Int
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.LocallyConstant.Basic
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

namespace AbelianTargets
end AbelianTargets
open AbelianTargets
variable {d : ℕ} {m K : ℕ} {i : Fin d}
namespace AbelianTargets.LowerCellCarrierMaps
end AbelianTargets.LowerCellCarrierMaps
open AbelianTargets
open AbelianTargets.LowerCellCarrierMaps
variable {K₀ : Fin d→ℕ} {T : IntegerRectangularTiling d K₀} {R : RectangularCell d}

theorem AbelianTargets.LowerCellCarrierMaps.boundaryValue_translate (F : LowerCellCarrierMaps T m K i R) (hR : R∈T.cells)
    (a : Fin d→ℤ) (G : LowerCellCarrierMaps (T.translate a) m K i (R.translate a))
    (hmap : ∀ (Q : RectangularCell d) (hQ : Q∈T.cells) (hr : Q.rank<R.rank)
      (z : CellClosedDomain Q),
      G.map (Q.translate a) (T.cell_translate hQ a)
        (by simpa only [RectangularCell.rank_translate] using hr) (Q.translateClosedPoint a z)=
        cellIntervalTranslate i a Q (F.map Q hQ hr z))
    (z : CellBoundaryDomain R) :
    G.boundaryValue (T.cell_translate hR a) (R.translateBoundaryPoint a z)=
      cellIntervalTranslate i a R (F.boundaryValue hR z) := by sorry
