-- Prove2me | Definitions.Def_AT260939824_IntegerCellGluing
-- name    : AT260939824_IntegerCellGluing
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T02:46:53.893157+00:00
-- url     : https://prove2.me/theorems/df0eb8cf-8803-4693-b6a7-d1062ae6bba8
-- title:
--   Global coordinate bounds from integer cells
-- statement:
--   A map from the real line to a pseudometric space with the same Lipschitz constant on every integer unit interval has that constant globally. For an integer rectangular cell, containing the midpoint of a coordinate unit interval forces containment of the whole interval along that coordinate line. These facts convert uniform cellwise coordinate estimates into global estimates without a factor depending on the number of crossed cells.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Sections 2-7; https://arxiv.org/html/2609.39824v1. Formalization-specific infrastructure in the import closure of Theorem 1.4 and Proposition 7.1; individual helper assertions are not represented as separately numbered paper theorems. Original Lean module AbelianTargets/IntegerCellGluing.lean, selected declaration lines 20-73, 77-101; SHA-256 86cad5706a28d360abc2a9adbbe62cbb9dbe256177f43e79cc6c5ca014d9f9dd. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_ParityCoordinates
import Definitions.Def_AT260939824_ParityFields
import Definitions.Def_AT260939824_Probability
import Definitions.Def_AT260939824_RectangularCells
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
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Constructions
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Separation.Profinite
import Mathlib.Topology.UniformSpace.HeineCantor

set_option autoImplicit false

/-!
# Global coordinate estimates from literal integer cells

On a coordinate line, any integer rectangle containing the midpoint of a
unit interval contains the entire interval. Consequently a uniform coordinate
estimate on covering cells gives the same estimate globally. This avoids any
loss proportional to the number of cells crossed by a line segment.
-/

namespace AbelianTargets

noncomputable section

open scoped NNReal

theorem lipschitz_real_of_integer_intervals {Z : Type*} [PseudoMetricSpace Z]
    (f : ℝ → Z) (K : ℝ≥0)
    (h : ∀ n : ℤ, ∀ x ∈ Set.Icc (n : ℝ) ((n : ℝ)+1),
      ∀ y ∈ Set.Icc (n : ℝ) ((n : ℝ)+1), dist (f x) (f y) ≤ K * |x-y|) :
    LipschitzWith K f := by
  have hint : ∀ n m : ℤ, n ≤ m → dist (f n) (f m) ≤ K * ((m : ℝ)-(n : ℝ)) := by
    intro n
    apply Int.leInduction
    · simp
    · intro m hnm ih
      have hm := h m m (by constructor <;> linarith)
        ((m : ℝ)+1) (by constructor <;> linarith)
      have he : |(m : ℝ)-((m : ℝ)+1)| = 1 := by norm_num
      rw [he, mul_one] at hm
      have ht := dist_triangle (f n) (f m) (f ((m : ℝ)+1))
      push_cast
      linarith
  have hordered : ∀ x y : ℝ, x ≤ y → dist (f x) (f y) ≤ K * (y-x) := by
    intro x y hxy
    let n := Int.floor x
    let m := Int.floor y
    have hnx : (n : ℝ) ≤ x := Int.floor_le x
    have hxn : x ≤ (n : ℝ)+1 := (Int.lt_floor_add_one x).le
    have hmy : (m : ℝ) ≤ y := Int.floor_le y
    have hym : y ≤ (m : ℝ)+1 := (Int.lt_floor_add_one y).le
    have hnm : n ≤ m := Int.floor_mono hxy
    by_cases he : n = m
    · have hh := h n x ⟨hnx,hxn⟩ y (by simpa [he] using And.intro hmy hym)
      rw [abs_of_nonpos (sub_nonpos.mpr hxy)] at hh
      simpa only [neg_sub] using hh
    · have hnm' : n+1 ≤ m := by omega
      have hx := h n x ⟨hnx,hxn⟩ ((n : ℝ)+1) (by constructor <;> linarith)
      have hy := h m (m : ℝ) (by constructor <;> linarith) y ⟨hmy,hym⟩
      rw [abs_of_nonpos (sub_nonpos.mpr hxn), neg_sub] at hx
      rw [abs_of_nonpos (sub_nonpos.mpr hmy), neg_sub] at hy
      have hi := hint (n+1) m hnm'
      push_cast at hi
      calc
        _ ≤ dist (f x) (f ((n : ℝ)+1)) + dist (f ((n : ℝ)+1)) (f y) :=
          dist_triangle _ _ _
        _ ≤ dist (f x) (f ((n : ℝ)+1)) +
            (dist (f ((n : ℝ)+1)) (f m) + dist (f m) (f y)) :=
          add_le_add le_rfl (dist_triangle _ _ _)
        _ ≤ K * ((n : ℝ)+1-x) + (K * ((m : ℝ)-((n : ℝ)+1)) + K*(y-(m : ℝ))) :=
          add_le_add hx (add_le_add hi hy)
        _ = K * (y-x) := by ring
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq]
  rcases le_total x y with hxy | hyx
  · rw [abs_of_nonpos (sub_nonpos.mpr hxy), neg_sub]
    exact hordered x y hxy
  · rw [dist_comm (f x) (f y), abs_of_nonneg (sub_nonneg.mpr hyx)]
    exact hordered y x hyx

namespace RectangularCell

/-- A rectangle with integer endpoints that contains a unit midpoint contains
the whole coordinate unit interval. -/
theorem coordinate_unit_interval {d : ℕ} (R : RectangularCell d)
    (z : RealCoordinates d) (i : Fin d) (n : ℤ)
    (hz : Function.update z i ((n : ℝ)+1/2) ∈ R.closedBox) :
    ∀ t ∈ Set.Icc (n : ℝ) ((n : ℝ)+1), Function.update z i t ∈ R.closedBox := by
  intro t ht j
  by_cases hji : j = i
  · subst j
    have hi := hz i
    simp only [Function.update_self] at hi ⊢
    have hlo : R.lower i ≤ n := by
      by_contra hbad
      have hh : n+1 ≤ R.lower i := by omega
      have hh' : (n : ℝ)+1 ≤ (R.lower i : ℝ) := by exact_mod_cast hh
      linarith
    have hhi : n+1 ≤ R.upper i := by
      by_contra hbad
      have hh : R.upper i ≤ n := by omega
      have hh' : (R.upper i : ℝ) ≤ (n : ℝ) := by exact_mod_cast hh
      linarith
    constructor
    · exact (show (R.lower i : ℝ) ≤ (n : ℝ) by exact_mod_cast hlo).trans ht.1
    · exact ht.2.trans (show (n : ℝ)+1 ≤ (R.upper i : ℝ) by exact_mod_cast hhi)
  · simpa only [Function.update_of_ne hji] using hz j

end RectangularCell





end

end AbelianTargets


