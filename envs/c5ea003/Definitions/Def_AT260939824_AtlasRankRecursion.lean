-- Prove2me | Definitions.Def_AT260939824_AtlasRankRecursion
-- name    : AT260939824_AtlasRankRecursion
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T02:58:22.945463+00:00
-- url     : https://prove2.me/theorems/4b65c854-957d-49e1-b8a7-8f74ce4d7ec0
-- title:
--   Compatible maps and extensions on rectangular skeleta
-- statement:
--   Fix a rectangular tiling $T$, carrier parameters $m,K$, and a distinguished coordinate $i$. A skeleton carrier family assigns a continuous map into each cell's own interval carrier to every cell below a specified rank. Whenever one cell is contained in another, the maps agree after the canonical carrier inclusion. A cell-extension record requires exact agreement with the resulting boundary map.
--
--   These definitions expose the compatibility invariant needed for rank-by-rank construction.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (2026), Section(s) 5; https://arxiv.org/abs/2609.39824v1. This item is auxiliary infrastructure of the accompanying formalization, not a claim that each implementation definition is separately numbered in the paper. Original Lean module AbelianTargets/AtlasRankRecursion.lean, selected declaration lines 12-19, 21-25, 32-35, 37-43, 48-50, 52-55; SHA-256 198106f4609a045b52672822067d62ac8f4bb91682cfd206d46b63a498a9ba02. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_AnisotropicMarkers
import Definitions.Def_AT260939824_AtlasBoundaryCarrierMaps
import Definitions.Def_AT260939824_AtlasBoxes
import Definitions.Def_AT260939824_CarrierCellRealization
import Definitions.Def_AT260939824_CarrierGeometry
import Definitions.Def_AT260939824_CarrierIntervalInclusion
import Definitions.Def_AT260939824_ClopenMarkers
import Definitions.Def_AT260939824_CompressedWords
import Definitions.Def_AT260939824_ContinuousAtlasPatterns
import Definitions.Def_AT260939824_ContinuousMarkerBoxes
import Definitions.Def_AT260939824_CovariantCuts
import Definitions.Def_AT260939824_DigitPathRealization
import Definitions.Def_AT260939824_Dimension
import Definitions.Def_AT260939824_FixedSlotInterpolation
import Definitions.Def_AT260939824_IntegerGridIntervals
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
import Definitions.Def_AT260939824_RectangularAtlasBoundary
import Definitions.Def_AT260939824_RectangularBoundaryStrata
import Definitions.Def_AT260939824_RectangularCells
import Definitions.Def_AT260939824_RectangularTranslation
import Definitions.Def_AT260939824_RegularAnisotropicAtlas
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
import Mathlib.Analysis.Normed.Module.RCLike.Real
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

/-! Rank recursion for actual atlas cells and literal interval carriers.
The local extension operator remains an explicit input; this module proves
the global compatibility bookkeeping and never assumes a global orbit map. -/

namespace AbelianTargets
noncomputable section
namespace IntegerRectangularTiling
variable {d : ℕ} {K₀ : Fin d → ℕ} (T : IntegerRectangularTiling d K₀)

theorem rank_lt_of_cells_subset_ne {P Q : RectangularCell d}
    (hP : P ∈ T.cells) (hQ : Q ∈ T.cells) (hsub : P.closedBox ⊆ Q.closedBox)
    (hne : P ≠ Q) : P.rank < Q.rank := by
  obtain ⟨z,hzP⟩ := P.relativeInterior_nonempty
  by_cases hzQ : z ∈ Q.relativeInterior
  · exact (hne (T.relativeInterior_unique hP hQ ⟨z,hzP,hzQ⟩)).elim
  · exact P.rank_lt_of_relativeInterior_on_boundary Q hsub hzP
      ⟨hsub (P.relativeInterior_subset hzP),hzQ⟩

theorem rank_le_of_cells_subset {P Q : RectangularCell d}
    (hP : P ∈ T.cells) (hQ : Q ∈ T.cells) (hsub : P.closedBox ⊆ Q.closedBox) : P.rank ≤ Q.rank := by
  by_cases he : P=Q
  · subst P; exact le_rfl
  · exact (T.rank_lt_of_cells_subset_ne hP hQ hsub he).le

end IntegerRectangularTiling

variable {d : ℕ} {K₀ : Fin d → ℕ} {T : IntegerRectangularTiling d K₀}
variable {m K : ℕ} {i : Fin d}

structure CellCarrierExtension {R : RectangularCell d}
    (F : LowerCellCarrierMaps T m K i R) (hR : R ∈ T.cells) where
  map : C(CellClosedDomain R,CellIntervalCarrier m K i R)
  boundary : ∀ z : CellBoundaryDomain R,map ⟨z.val,z.property.1⟩=F.boundaryValue hR z

structure SkeletonCarrierMaps (T : IntegerRectangularTiling d K₀) (m K : ℕ) (i : Fin d) (n : ℕ) where
  map : ∀ R : RectangularCell d,R ∈ T.cells → R.rank < n →
    C(CellClosedDomain R,CellIntervalCarrier m K i R)
  compatible : ∀ (P Q : RectangularCell d) (hP : P ∈ T.cells) (hQ : Q ∈ T.cells)
    (hrP : P.rank < n) (hrQ : Q.rank < n) (hsub : P.closedBox ⊆ Q.closedBox)
    (z : CellClosedDomain P),
    cellIntervalInclude i hsub (map P hP hrP z)=map Q hQ hrQ ⟨z.val,hsub z.property⟩

namespace SkeletonCarrierMaps
variable {n : ℕ}

def empty : SkeletonCarrierMaps T m K i 0 where
  map R hR hr := (Nat.not_lt_zero R.rank hr).elim
  compatible P Q hP hQ hrP hrQ hs z := (Nat.not_lt_zero P.rank hrP).elim

def lowerFamily (F : SkeletonCarrierMaps T m K i n) (R : RectangularCell d)
    (he : R.rank=n) : LowerCellCarrierMaps T m K i R where
  map Q hQ hr := F.map Q hQ (by omega)
  compatible P Q hP hQ hrP hrQ hs z := F.compatible P Q hP hQ (by omega) (by omega) hs z

variable (extend : ∀ (R : RectangularCell d) (hR : R ∈ T.cells)
  (F : LowerCellCarrierMaps T m K i R),CellCarrierExtension F hR)









end SkeletonCarrierMaps



end
end AbelianTargets


