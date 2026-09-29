-- Prove2me | solution 1 for bernoulli_rademacher_moment_bound_by_conditional_khintchine_scales_of_sample_ratio
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T19:32:34.662691+00:00
-- url     : https://prove2.me/submissions/752d7192-26e8-40db-a416-91b1ee9e89a7

import Definitions.Def_matrix_completion_rademacher
import Mathlib.Tactic

open MatrixCompletion

open scoped Classical BigOperators

private lemma bernoulliObservationWeight_nonneg
    {n₁ n₂ : ℕ} {p : ℝ} (hp : 0 ≤ p) (hp_one : p ≤ 1)
    (Omega : Finset (Fin n₁ × Fin n₂)) :
    0 ≤ bernoulliObservationWeight p Omega := by
  unfold bernoulliObservationWeight
  exact mul_nonneg (pow_nonneg hp _)
    (pow_nonneg (sub_nonneg.mpr hp_one) _)

private lemma bernoulliExpectation_mono
    {n₁ n₂ : ℕ} {p : ℝ} (hp : 0 ≤ p) (hp_one : p ≤ 1)
    {F G : Finset (Fin n₁ × Fin n₂) → ℝ} :
    (∀ Omega, F Omega ≤ G Omega) →
    bernoulliExpectation p F ≤ bernoulliExpectation p G := by
  intro hFG
  unfold bernoulliExpectation
  apply Finset.sum_le_sum
  intro Omega _
  exact mul_le_mul_of_nonneg_left (hFG Omega)
    (bernoulliObservationWeight_nonneg hp hp_one Omega)

private lemma sample_ratio_nonneg
    {n₁ n₂ m : ℕ} :
    0 ≤ ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) := by
  exact div_nonneg (Nat.cast_nonneg _)
    (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

private lemma sample_ratio_le_one
    {n₁ n₂ m : ℕ} :
    0 < n₁ → 0 < n₂ → m ≤ n₁ * n₂ →
    ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) ≤ 1 := by
  intro hn₁ hn₂ hm
  have hden_pos : 0 < (n₁ : ℝ) * (n₂ : ℝ) :=
    mul_pos (Nat.cast_pos.mpr hn₁) (Nat.cast_pos.mpr hn₂)
  have hnum_le_den : (m : ℝ) ≤ (n₁ : ℝ) * (n₂ : ℝ) := by
    exact_mod_cast hm
  rw [div_le_iff₀ hden_pos]
  simpa using hnum_le_den

theorem solution
    (Ckh : ℝ) :
    ∀ (n₁ n₂ m q : ℕ) (X : Matrix (Fin n₁) (Fin n₂) ℝ),
      0 < n₁ → 0 < n₂ → m ≤ n₁ * n₂ →
      (∀ Omega : Finset (Fin n₁ × Fin n₂),
        rademacherExpectation
            (fun eps =>
              spectralNorm
                (rademacherSampledMatrix Omega eps
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ q) ≤
          (Ckh * Real.sqrt (q : ℝ) *
            (((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹) *
            Real.sqrt
              (max (sampledRowEnergyMax Omega X)
                (sampledColumnEnergyMax Omega X))) ^ q) →
      bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
          (fun Omega =>
            rademacherExpectation
              (fun eps =>
                spectralNorm
                  (rademacherSampledMatrix Omega eps
                    ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ q)) ≤
        bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
          (fun Omega =>
            (Ckh * Real.sqrt (q : ℝ) *
              (((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹) *
              Real.sqrt
                (max (sampledRowEnergyMax Omega X)
                  (sampledColumnEnergyMax Omega X))) ^ q) := by
  intro n₁ n₂ m q X hn₁ hn₂ hm hPointwise
  exact bernoulliExpectation_mono sample_ratio_nonneg
    (sample_ratio_le_one hn₁ hn₂ hm) hPointwise
