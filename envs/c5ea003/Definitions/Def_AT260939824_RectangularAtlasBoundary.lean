-- Prove2me | Definitions.Def_AT260939824_RectangularAtlasBoundary
-- name    : AT260939824_RectangularAtlasBoundary
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T02:48:09.480226+00:00
-- url     : https://prove2.me/theorems/923522d7-7ab0-4bab-9f90-8946e49bba56
-- title:
--   Finite boundary-cell families and strict rank decrease
-- statement:
--   Let $T$ be an integer rectangular tiling of $\mathbb R^d$ with bounded side lengths, and let its cells be the intersections of the incident tile faces at each point. For a rectangle $R$, define the finite boundary-cell family
--   $$\mathcal B_T(R)=\{Q\in\operatorname{Cells}(T):Q\subseteq R,\ \operatorname{rank}Q<\operatorname{rank}R\},$$
--   where containment means containment of closed boxes and rank counts coordinates of positive width. If $R,Q$ are tiling cells with the indicated containment and strict rank inequality, the whole closed box of $Q$ lies in the relative boundary of $R$. Conversely a point in the relative boundary has a containing point-cell of strictly smaller rank. These properties support recursion on cell rank.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Sections 2–7, supporting construction for Theorem 1.4 and Proposition 7.1; https://arxiv.org/html/2609.39824v1. Formalization-specific infrastructure in the import closure; individual helper assertions are not represented as separately numbered paper theorems. Original Lean module AbelianTargets/RectangularAtlasBoundary.lean, selected declaration lines 11-27, 34-37, 39-53, 55-59, 61-63; SHA-256 502e7b10867367620a0eab367ea2d7d09a069ca1d45c95029c42c57864ca1ac0. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_FiniteRectangleIntersections
import Definitions.Def_AT260939824_ParityCoordinates
import Definitions.Def_AT260939824_ParityFields
import Definitions.Def_AT260939824_Probability
import Definitions.Def_AT260939824_RectangularBoundaryStrata
import Definitions.Def_AT260939824_RectangularCells
import Definitions.Def_AT260939824_RectangularFaceRefinement
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
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Interval
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Constructions
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Separation.Profinite
import Mathlib.Topology.UniformSpace.HeineCantor

set_option autoImplicit false

/-! Finite, strictly lower-rank boundary refinements of the actual point cells. -/

namespace AbelianTargets
noncomputable section

namespace RectangularCell
variable {d : ℕ}

theorem rank_lt_of_relativeInterior_on_boundary (R Q : RectangularCell d)
    (hsub : R.closedBox ⊆ Q.closedBox) {z : RealCoordinates d}
    (hzR : z ∈ R.relativeInterior) (hzQ : z ∈ Q.boundary) : R.rank < Q.rank := by
  obtain ⟨i,hi,hend⟩ := Q.boundary_has_endpoint hzQ
  apply R.rank_lt_of_subset_and_collapsed Q hsub
  refine ⟨i,hi,?_⟩
  by_contra hne
  have hz := hzR i
  simp only [relativeInterior,hne,if_false] at hz
  have hb := (closedBox_subset_iff R Q).mp hsub i
  have hlo : (Q.lower i : ℝ) ≤ (R.lower i : ℝ) := by exact_mod_cast hb.1
  have hhi : (R.upper i : ℝ) ≤ (Q.upper i : ℝ) := by exact_mod_cast hb.2
  rcases hend with he | he
  · rw [he] at hz
    exact (not_lt_of_ge hlo) hz.1
  · rw [he] at hz
    exact (not_lt_of_ge hhi) hz.2

end RectangularCell

namespace IntegerRectangularTiling
variable {d : ℕ} {K : Fin d → ℕ} (T : IntegerRectangularTiling d K)

theorem pointCell_rank_lt_on_boundary (x z : RealCoordinates d)
    (hz : z ∈ (T.pointCell x).boundary) : (T.pointCell z).rank < (T.pointCell x).rank :=
  RectangularCell.rank_lt_of_relativeInterior_on_boundary _ _
    (T.pointCell_closed_mono x z hz.1) (T.mem_relativeInterior_pointCell z) hz

theorem contained_cell_closed_subset_boundary {R Q : RectangularCell d}
    (hR : R ∈ T.cells) (hQ : Q ∈ T.cells) (hsub : Q.closedBox ⊆ R.closedBox)
    (hrank : Q.rank < R.rank) : Q.closedBox ⊆ R.boundary := by
  obtain ⟨x,rfl⟩ := hR
  obtain ⟨y,rfl⟩ := hQ
  intro z hz
  refine ⟨hsub hz,?_⟩
  intro hzR
  have he := T.pointCell_constant x z hzR
  have hback := T.pointCell_closed_mono y z hz
  rw [he] at hback
  have heq : T.pointCell y = T.pointCell x :=
    RectangularCell.closedBox_injective (Set.Subset.antisymm hsub hback)
  rw [heq] at hrank
  exact (lt_irrefl _) hrank

def boundaryCells (R : RectangularCell d) : Finset (RectangularCell d) :=
  ((T.finite_cells_contained R).subset (by
    intro Q hQ
    exact ⟨hQ.1,hQ.2.1⟩) :
      {Q : RectangularCell d | Q ∈ T.cells ∧ Q.closedBox ⊆ R.closedBox ∧ Q.rank < R.rank}.Finite).toFinset

@[simp] theorem mem_boundaryCells (R Q : RectangularCell d) :
    Q ∈ T.boundaryCells R ↔ Q ∈ T.cells ∧ Q.closedBox ⊆ R.closedBox ∧ Q.rank < R.rank :=
  Set.Finite.mem_toFinset _



end IntegerRectangularTiling
end
end AbelianTargets


