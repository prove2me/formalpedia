-- Prove2me | solution 2 for rademacher_sampled_matrix_noncommutative_khintchine_diagonal_gram_bound_q2
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:05:46.911793+00:00
-- url     : https://prove2.me/submissions/9e307424-9b5b-4b72-b855-b73115bfbb84

import Definitions.Def_matrix_completion_gram_schatten
import Theorems.Thm_rademacher_sampled_matrix_schatten_moment_khintchine_q_ge_two_variance_scale

open MatrixCompletion
open scoped BigOperators

private lemma scaled_sqrt_sup_le_gram {I : Type*} [Fintype I]
    (e : I → ℝ) (p q : ℝ) (hp : 0 ≤ p) (hq : 0 < q) :
    p⁻¹ * Real.sqrt (⨆ i, e i) ≤
      (∑ i, (p⁻¹ * Real.sqrt (e i)) ^ q) ^ q⁻¹ := by
  classical
  cases isEmpty_or_nonempty I with
  | inl h =>
    simp only [Real.iSup_of_isEmpty, Real.sqrt_zero, mul_zero,
      Finset.sum_of_isEmpty]
    exact Real.rpow_nonneg (by norm_num) _
  | inr h =>
    obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := e)
    rw [← hi]
    have hterm : 0 ≤ p⁻¹ * Real.sqrt (e i) := by positivity
    have hsum : (p⁻¹ * Real.sqrt (e i)) ^ q ≤
        ∑ j, (p⁻¹ * Real.sqrt (e j)) ^ q :=
      Finset.single_le_sum (fun j _ => Real.rpow_nonneg
        (mul_nonneg (inv_nonneg.mpr hp) (Real.sqrt_nonneg (e j))) q)
        (Finset.mem_univ i)
    calc p⁻¹ * Real.sqrt (e i)
        = ((p⁻¹ * Real.sqrt (e i)) ^ q) ^ q⁻¹ := by
            rw [← Real.rpow_mul hterm, mul_inv_cancel₀ hq.ne', Real.rpow_one]
      _ ≤ (∑ j, (p⁻¹ * Real.sqrt (e j)) ^ q) ^ q⁻¹ :=
        Real.rpow_le_rpow (Real.rpow_nonneg hterm _) hsum (by positivity)

private lemma variance_scale_le_gram {n₁ n₂ : ℕ}
    (Omega : Finset (Fin n₁ × Fin n₂)) (p q : ℝ)
    (X : Matrix (Fin n₁) (Fin n₂) ℝ) (hp : 0 ≤ p) (hq : 0 < q) :
    rademacherSampledVarianceScale Omega p X ≤
      max (sampledRowGramSchatten Omega p X q)
        (sampledColumnGramSchatten Omega p X q) := by
  have hrow : p⁻¹ * Real.sqrt (sampledRowEnergyMax Omega X) ≤
      sampledRowGramSchatten Omega p X q := by
    exact scaled_sqrt_sup_le_gram _ p q hp hq
  have hcol : p⁻¹ * Real.sqrt (sampledColumnEnergyMax Omega X) ≤
      sampledColumnGramSchatten Omega p X q := by
    exact scaled_sqrt_sup_le_gram _ p q hp hq
  unfold rademacherSampledVarianceScale
  rcases le_total (sampledRowEnergyMax Omega X) (sampledColumnEnergyMax Omega X) with h | h
  · rw [max_eq_right h]
    exact hcol.trans (le_max_right _ _)
  · rw [max_eq_left h]
    exact hrow.trans (le_max_left _ _)

theorem solution :
    ∃ C : ℝ, 0 < C ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ m q : ℕ)
        (Omega : Finset (Fin n₁ × Fin n₂))
        (X : Matrix (Fin n₁) (Fin n₂) ℝ),
        2 ≤ q →
        (q : ℝ) ≥ β * Real.log (↑(max n₁ n₂)) →
        rademacherExpectation
            (fun eps =>
              schattenNorm (q : ℝ)
                (rademacherSampledMatrix Omega eps
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ q) ≤
          (C * Real.sqrt (q : ℝ) *
            max (sampledRowGramSchatten Omega
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X (q : ℝ))
                (sampledColumnGramSchatten Omega
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X (q : ℝ))) ^ q := by
  obtain ⟨C, hC, hbound⟩ :=
    rademacher_sampled_matrix_schatten_moment_khintchine_q_ge_two_variance_scale
  refine ⟨C, hC, ?_⟩
  intro β hβ n₁ n₂ m q Omega X hq hlog
  refine (hbound C le_rfl β hβ n₁ n₂ m q Omega X hq hlog).trans ?_
  apply pow_le_pow_left₀
  · unfold rademacherSampledVarianceScale
    positivity
  · apply mul_le_mul_of_nonneg_left
    · exact variance_scale_le_gram Omega _ _ X (by positivity) (by exact_mod_cast (show 0 < q by omega))
    · positivity

#print axioms solution
