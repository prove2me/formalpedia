-- Prove2me | Definitions.Def_AT260939824_RectangularFaceRefinement
-- name    : AT260939824_RectangularFaceRefinement
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T02:46:21.181754+00:00
-- url     : https://prove2.me/theorems/6d7504ac-bea5-4c34-a2f9-92cf10e20518
-- title:
--   Face refinement and rank comparison for rectangular cells
-- statement:
--   Let $R,Q$ be integer rectangles in $\mathbb R^d$. Containment of their closed boxes implies inclusion of their sets of varying axes. If some axis varies in $Q$ but is collapsed in $R$, then
--   $$R\subseteq Q\quad\Longrightarrow\quad\operatorname{rank}R<\operatorname{rank}Q.$$
--   For a positive-width rectangle $Q$, its face at $x$ is constant as a second point varies in that face's relative interior; moving to a point in its closed face can only produce a smaller face. Every point of the relative boundary of any rectangle equals an endpoint on at least one varying axis. These are coordinatewise face-refinement facts, including degenerate boundary cells.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Sections 2–7, supporting construction for Theorem 1.4 and Proposition 7.1; https://arxiv.org/html/2609.39824v1. Formalization-specific infrastructure in the import closure; individual helper assertions are not represented as separately numbered paper theorems. Original Lean module AbelianTargets/RectangularFaceRefinement.lean, selected declaration lines 8-30, 32-51, 53-58, 60-70, 72-89; SHA-256 8c3c6eb7eef64d0c903ee6f2bab374e99ed0b6988ff8c8ca2477f8fe91b14cb7. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_FiniteRectangleIntersections
import Definitions.Def_AT260939824_ParityCoordinates
import Definitions.Def_AT260939824_ParityFields
import Definitions.Def_AT260939824_Probability
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

namespace AbelianTargets
noncomputable section
namespace RectangularCell
variable {d : ℕ}

theorem faceAt_eq_of_relativeInterior (R : RectangularCell d)
    (hpos : ∀ i,R.lower i < R.upper i) (x y : RealCoordinates d)
    (hy : y ∈ (R.faceAt x).relativeInterior) : R.faceAt y = R.faceAt x := by
  have h : ∀ i,(R.faceAt y).lower i = (R.faceAt x).lower i ∧
      (R.faceAt y).upper i = (R.faceAt x).upper i := by
    intro i
    have hne := ne_of_lt (hpos i)
    have hne' : (R.lower i : ℝ) ≠ (R.upper i : ℝ) := by exact_mod_cast hne
    have hyi := hy i
    by_cases hu : x i = (R.upper i : ℝ)
    · have hl : x i ≠ (R.lower i : ℝ) := by rw [hu]; exact hne'.symm
      simp [faceAt,hu,hl,hne',hne'.symm] at hyi
      have hyl : y i ≠ (R.lower i : ℝ) := by rw [hyi]; exact hne'.symm
      simp [faceAt,hu,hl,hyi,hyl,hne',hne'.symm]
    · by_cases hl : x i = (R.lower i : ℝ)
      · simp [faceAt,hu,hl,hne',hne'.symm] at hyi
        have hyu : y i ≠ (R.upper i : ℝ) := by rw [hyi]; exact hne'
        simp [faceAt,hu,hl,hyi,hyu,hne',hne'.symm]
      · simp only [faceAt,hu,hl,if_false,hne] at hyi
        have hyl : y i ≠ (R.lower i : ℝ) := ne_of_gt hyi.1
        have hyu : y i ≠ (R.upper i : ℝ) := ne_of_lt hyi.2
        simp [faceAt,hu,hl,hyl,hyu]
  exact endpoint_pair_injective (Prod.ext (funext (fun i => (h i).1)) (funext (fun i => (h i).2)))

theorem faceAt_mono (R : RectangularCell d) (hpos : ∀ i,R.lower i < R.upper i)
    (x z : RealCoordinates d) (hz : z ∈ (R.faceAt x).closedBox) :
    (R.faceAt z).closedBox ⊆ (R.faceAt x).closedBox := by
  intro w hw i
  have hne : (R.lower i : ℝ) ≠ (R.upper i : ℝ) := by exact_mod_cast ne_of_lt (hpos i)
  have hzi := hz i
  have hwi := hw i
  by_cases hu : x i = (R.upper i : ℝ)
  · have hl : x i ≠ (R.lower i : ℝ) := by rw [hu]; exact hne.symm
    simp [faceAt,hu,hl,hne,hne.symm] at hzi ⊢
    have hze : z i = (R.upper i : ℝ) := le_antisymm hzi.2 hzi.1
    have hzl : z i ≠ (R.lower i : ℝ) := by rw [hze]; exact hne.symm
    simpa [faceAt,hze,hzl,hne,hne.symm] using hwi
  · by_cases hl : x i = (R.lower i : ℝ)
    · simp [faceAt,hu,hl,hne,hne.symm] at hzi ⊢
      have hze : z i = (R.lower i : ℝ) := le_antisymm hzi.2 hzi.1
      have hzu : z i ≠ (R.upper i : ℝ) := by rw [hze]; exact hne
      simpa [faceAt,hze,hzu,hne,hne.symm] using hwi
    · simp only [faceAt,hu,hl,if_false]
      exact R.faceAt_subset z hw i

theorem varyingAxes_subset_of_closedBox_subset (R Q : RectangularCell d)
    (hsub : R.closedBox ⊆ Q.closedBox) : R.varyingAxes ⊆ Q.varyingAxes := by
  intro i hi
  simp only [varyingAxes,Finset.mem_filter,Finset.mem_univ,true_and] at hi ⊢
  have h := (closedBox_subset_iff R Q).mp hsub i
  omega

theorem rank_lt_of_subset_and_collapsed (R Q : RectangularCell d)
    (hsub : R.closedBox ⊆ Q.closedBox)
    (hcollapse : ∃ i,Q.lower i < Q.upper i ∧ R.lower i = R.upper i) : R.rank < Q.rank := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨varyingAxes_subset_of_closedBox_subset R Q hsub,?_⟩
  intro he
  obtain ⟨i,hi,hR⟩ := hcollapse
  have hiQ : i ∈ Q.varyingAxes := by simp [varyingAxes,hi]
  rw [← he] at hiQ
  simpa [varyingAxes,hR] using hiQ

theorem boundary_has_endpoint (R : RectangularCell d) {z : RealCoordinates d}
    (hz : z ∈ R.boundary) :
    ∃ i,R.lower i < R.upper i ∧
      (z i = (R.lower i : ℝ) ∨ z i = (R.upper i : ℝ)) := by
  obtain ⟨hz,hnot⟩ := hz
  change ¬(∀ i,if R.lower i = R.upper i then z i = (R.lower i : ℝ)
    else (R.lower i : ℝ) < z i ∧ z i < (R.upper i : ℝ)) at hnot
  obtain ⟨i,hi⟩ := not_forall.mp hnot
  by_cases he : R.lower i = R.upper i
  · have hz' : z i = (R.lower i : ℝ) := le_antisymm (by simpa only [he] using (hz i).2) (hz i).1
    exact (hi (by simpa only [he,if_true] using hz')).elim
  · refine ⟨i,lt_of_le_of_ne (R.ordered i) he,?_⟩
    simp only [he,if_false,not_and] at hi
    by_cases hlo : (R.lower i : ℝ) < z i
    · right
      exact le_antisymm (hz i).2 (le_of_not_gt (hi hlo))
    · left
      exact le_antisymm (le_of_not_gt hlo) (hz i).1

end RectangularCell
end
end AbelianTargets


