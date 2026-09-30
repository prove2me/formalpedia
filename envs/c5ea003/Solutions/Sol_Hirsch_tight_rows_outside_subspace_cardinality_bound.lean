-- Prove2me | solution 1 for Hirsch.tight_rows_outside_subspace_cardinality_bound
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-10T22:59:53.645379+00:00
-- url     : https://prove2.me/submissions/d81b3bfc-ac7a-4ce5-9308-cd2746724c0d

import Mathlib
import Definitions.Def_Hirsch_model
open scoped BigOperators RealInnerProductSpace
open Set Hirsch
set_option autoImplicit false
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 12000000

namespace HirschPolynomialAccess

theorem vertex_tight_rows_span_checked
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
    · have hs : 0 < b i - ⟪a i, x⟫ := sub_pos.mpr (lt_of_le_of_ne (hx.1 i) hi)
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

end HirschPolynomialAccess
namespace HirschRankFaceCover

theorem tight_rows_outside_subspace_card_ge_codim
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x : EuclideanSpace ℝ (Fin d))
    (hx : x ∈ extremePoints ℝ (Hpoly a b))
    (U : Submodule ℝ (EuclideanSpace ℝ (Fin d))) :
    d - Module.finrank ℝ U ≤
      (Finset.univ.filter (fun i => a i ∉ U ∧ ⟪a i, x⟫ = b i)).card := by
  classical
  let S : Finset (Fin n) :=
    Finset.univ.filter (fun i => a i ∉ U ∧ ⟪a i, x⟫ = b i)
  let T : Uᗮ →ₗ[ℝ] (S → ℝ) :=
    { toFun := fun y i => ⟪a i.1, (y : EuclideanSpace ℝ (Fin d))⟫
      map_add' := by
        intro y z
        funext i
        simp [inner_add_right]
      map_smul' := by
        intro c y
        funext i
        simp [inner_smul_right] }
  have hinj : Function.Injective T := by
    intro y z hyz
    apply Subtype.ext
    apply sub_eq_zero.mp
    apply HirschPolynomialAccess.vertex_tight_rows_span_checked d n a b x hx
    intro i hi
    by_cases hai : a i ∈ U
    · have hy : ⟪a i, (y : EuclideanSpace ℝ (Fin d))⟫ = 0 :=
        (U.mem_orthogonal _).mp y.2 (a i) hai
      have hz : ⟪a i, (z : EuclideanSpace ℝ (Fin d))⟫ = 0 :=
        (U.mem_orthogonal _).mp z.2 (a i) hai
      rw [inner_sub_right, hy, hz, sub_self]
    · have hiS : i ∈ S := by simp [S, hai, hi]
      have hcoord := congrFun hyz ⟨i, hiS⟩
      change ⟪a i, (y : EuclideanSpace ℝ (Fin d))⟫ =
        ⟪a i, (z : EuclideanSpace ℝ (Fin d))⟫ at hcoord
      rw [inner_sub_right, hcoord, sub_self]
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  have hcod : Module.finrank ℝ (S → ℝ) = S.card := by
    simp [Fintype.card_coe]
  have hdim : Module.finrank ℝ U + Module.finrank ℝ Uᗮ = d := by
    simpa only [finrank_euclideanSpace_fin] using U.finrank_add_finrank_orthogonal
  change d - Module.finrank ℝ U ≤ S.card
  rw [hcod] at hle
  omega

end HirschRankFaceCover

theorem solution {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x : EuclideanSpace ℝ (Fin d))
    (hx : x ∈ extremePoints ℝ (Hpoly a b))
    (U : Submodule ℝ (EuclideanSpace ℝ (Fin d))) :
    d - Module.finrank ℝ U ≤
      (Finset.univ.filter (fun i => a i ∉ U ∧ ⟪a i, x⟫ = b i)).card := by
  exact HirschRankFaceCover.tight_rows_outside_subspace_card_ge_codim a b x hx U

#print axioms solution
