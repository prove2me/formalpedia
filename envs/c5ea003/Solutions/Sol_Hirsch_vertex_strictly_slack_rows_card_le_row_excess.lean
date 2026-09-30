-- Prove2me | solution 1 for Hirsch.vertex_strictly_slack_rows_card_le_row_excess
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-12T11:22:25.879979+00:00
-- url     : https://prove2.me/submissions/8dc241ef-cb1e-4eec-9423-a424b559d380

import Mathlib
import Definitions.Def_Hirsch_model

open scoped RealInnerProductSpace
open Set

set_option autoImplicit false
set_option maxHeartbeats 5000000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace Hirsch

/-- Direct finite-perturbation fact: rows tight at a vertex span the ambient
space. Kept private so the public theorem below has no private repository
dependencies beyond the public Hirsch model. -/
private theorem vertexSlack_tight_rows_span
    (d n : ℕ)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x : EuclideanSpace ℝ (Fin d))
    (hx : x ∈ extremePoints ℝ (Hpoly a b))
    (y : EuclideanSpace ℝ (Fin d))
    (horth : ∀ i, ⟪a i, x⟫ = b i → ⟪a i, y⟫ = 0) :
    y = 0 := by
  classical
  have hlocal : ∀ i : Fin n, ∃ t : ℝ,
      0 < t ∧ t * |⟪a i, y⟫| ≤ b i - ⟪a i, x⟫ := by
    intro i
    by_cases hi : ⟪a i, x⟫ = b i
    · refine ⟨1, zero_lt_one, ?_⟩
      rw [horth i hi, abs_zero, mul_zero, hi, sub_self]
    · have hs : 0 < b i - ⟪a i, x⟫ :=
        sub_pos.mpr (lt_of_le_of_ne (hx.1 i) hi)
      have hd : 0 < |⟪a i, y⟫| + 1 := by positivity
      let t : ℝ := (b i - ⟪a i, x⟫) / (|⟪a i, y⟫| + 1)
      have ht : 0 < t := div_pos hs hd
      have hprod : t * (|⟪a i, y⟫| + 1) = b i - ⟪a i, x⟫ := by
        dsimp [t]
        exact div_mul_cancel₀ _ (ne_of_gt hd)
      exact ⟨t, ht, by nlinarith⟩
  choose e hepos hebound using hlocal
  have huniform : ∀ S : Finset (Fin n), ∃ t : ℝ,
      0 < t ∧ ∀ i ∈ S, t ≤ e i := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact ⟨1, zero_lt_one, by simp⟩
    | @insert i S hi ih =>
      obtain ⟨t, ht, hti⟩ := ih
      refine ⟨min (e i) t, lt_min (hepos i) ht, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with hji | hjS
      · subst j
        exact min_le_left _ _
      · exact (min_le_right _ _).trans (hti j hjS)
  obtain ⟨t, ht, hte⟩ := huniform Finset.univ
  have hbudget : ∀ i, t * |⟪a i, y⟫| ≤ b i - ⟪a i, x⟫ := by
    intro i
    exact (mul_le_mul_of_nonneg_right (hte i (Finset.mem_univ i))
      (abs_nonneg _)).trans (hebound i)
  have hp : x + t • y ∈ Hpoly a b := by
    intro i
    have hmul := mul_le_mul_of_nonneg_left (le_abs_self ⟪a i, y⟫) ht.le
    rw [inner_add_right, inner_smul_right]
    linarith [hbudget i]
  have hm : x - t • y ∈ Hpoly a b := by
    intro i
    have hmul := mul_le_mul_of_nonneg_left (neg_le_abs ⟪a i, y⟫) ht.le
    rw [mul_neg] at hmul
    rw [inner_sub_right, inner_smul_right]
    linarith [hbudget i]
  have hmid : x ∈ openSegment ℝ (x + t • y) (x - t • y) := by
    refine ⟨(1 / 2 : ℝ), (1 / 2 : ℝ), by norm_num, by norm_num,
      by norm_num, ?_⟩
    module
  have hpeq : x + t • y = x := hx.2 hp hm hmid
  have hty : t • y = 0 := by
    have h := congrArg (fun z => z - x) hpeq
    simpa using h
  exact (smul_eq_zero.mp hty).resolve_left (ne_of_gt ht)

/-- At a vertex of an `n`-row H-presentation in dimension `d`, at most `n-d`
rows are strictly slack. Equivalently, at least `d` describing rows are tight.
No boundedness, irredundancy, or full-dimensionality assumption is used. -/
theorem vertex_strictly_slack_rows_card_le_row_excess
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (v : EuclideanSpace ℝ (Fin d))
    (hv : v ∈ extremePoints ℝ (Hpoly a b)) :
    (Finset.univ.filter (fun i => ⟪a i, v⟫ < b i)).card ≤ n - d := by
  classical
  let T : Finset (Fin n) := Finset.univ.filter (fun i => ⟪a i, v⟫ = b i)
  let J : Finset (Fin n) := Finset.univ.filter (fun i => ⟪a i, v⟫ < b i)
  let A : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] (T → ℝ) :=
    { toFun := fun x i => ⟪a i.1, x⟫
      map_add' := by
        intro x y
        funext i
        simp [inner_add_right]
      map_smul' := by
        intro c x
        funext i
        simp [inner_smul_right] }
  have hAinj : Function.Injective A := by
    intro x y hxy
    apply sub_eq_zero.mp
    apply vertexSlack_tight_rows_span d n a b v hv (x - y)
    intro i hi
    have hiT : i ∈ T := by
      simp [T, hi]
    have hcoord := congrFun hxy ⟨i, hiT⟩
    change ⟪a i, x⟫ = ⟪a i, y⟫ at hcoord
    rw [inner_sub_right, hcoord, sub_self]
  have hdim : d ≤ T.card := by
    have hle := LinearMap.finrank_le_finrank_of_injective hAinj
    have hdom : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = d :=
      finrank_euclideanSpace_fin (𝕜 := ℝ)
    have hcod : Module.finrank ℝ (T → ℝ) = T.card := by simp
    rw [hdom, hcod] at hle
    exact hle
  have hpart : J = Finset.univ \ T := by
    ext i
    simp only [J, T, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_sdiff]
    constructor
    · intro hlt
      exact ne_of_lt hlt
    · intro hne
      exact lt_of_le_of_ne (hv.1 i) hne
  have hcard : J.card + T.card = n := by
    rw [hpart]
    have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ T)
    simpa using h
  change J.card ≤ n - d
  omega

#print axioms vertex_strictly_slack_rows_card_le_row_excess

end Hirsch


theorem solution
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (v : EuclideanSpace ℝ (Fin d))
    (hv : v ∈ Set.extremePoints ℝ (Hirsch.Hpoly a b)) :
    (Finset.univ.filter (fun i => ⟪a i, v⟫ < b i)).card ≤ n - d := by
  exact Hirsch.vertex_strictly_slack_rows_card_le_row_excess a b v hv

#print axioms solution
