-- Prove2me | solution 1 for bernoulli_expectation_sqrt_self_bound_of_positive_rate_pointwise_gram_bound
-- status  : ACCEPTED   (prove)
-- author  : @Minghui
-- created : 2026-06-26T02:14:56.454234+00:00
-- url     : https://prove2.me/submissions/6d5d95a1-bfc0-412a-b85d-3b819d2d35f4

import Definitions.Def_matrix_completion_bernoulli
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.BigOperators.Ring.Finset

open MatrixCompletion
open scoped Classical BigOperators

private theorem bernoulliObservationWeight_nonneg_of_nonneg_rate
    {n₁ n₂ : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (Omega : Finset (Fin n₁ × Fin n₂)) :
    0 ≤ bernoulliObservationWeight p Omega := by
  unfold bernoulliObservationWeight
  exact mul_nonneg (pow_nonneg hp0 _) (pow_nonneg (sub_nonneg.mpr hp1) _)

private theorem bernoulliObservationWeight_sum_eq_one
    {n₁ n₂ : ℕ} {p : ℝ} :
    (∑ Omega : Finset (Fin n₁ × Fin n₂), bernoulliObservationWeight p Omega) = 1 := by
  classical
  unfold bernoulliObservationWeight
  simpa using
    (Fintype.sum_pow_mul_eq_add_pow (Fin n₁ × Fin n₂) p (1 - p) :
      (∑ s : Finset (Fin n₁ × Fin n₂),
        p ^ s.card * (1 - p) ^ (Fintype.card (Fin n₁ × Fin n₂) - s.card)) =
          (p + (1 - p)) ^ Fintype.card (Fin n₁ × Fin n₂))

theorem solution
    {n₁ n₂ : ℕ} {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1)
    (g z : Finset (Fin n₁ × Fin n₂) → ℝ)
    (hg : ∀ Ω, 0 ≤ g Ω)
    (hbound : ∀ Ω, g Ω ≤ p * (z Ω + 1)) :
    bernoulliExpectation p (fun Ω => Real.sqrt (p⁻¹ * g Ω)) ≤
      Real.sqrt (bernoulliExpectation p z + 1) := by
  classical
  let w : Finset (Fin n₁ × Fin n₂) → ℝ := fun Ω => bernoulliObservationWeight p Ω
  have hp0 : 0 ≤ p := le_of_lt hp
  have hw : ∀ Ω, 0 ≤ w Ω :=
    fun Ω => bernoulliObservationWeight_nonneg_of_nonneg_rate hp0 hp1 Ω
  have hwsum : (∑ Ω, w Ω) = 1 := by
    simpa [w] using
      (bernoulliObservationWeight_sum_eq_one (n₁ := n₁) (n₂ := n₂) (p := p))
  have hnonneg_z1 : ∀ Ω : Finset (Fin n₁ × Fin n₂), 0 ≤ z Ω + 1 := by
    intro Ω
    have hpz_nonneg : 0 ≤ p * (z Ω + 1) := le_trans (hg Ω) (hbound Ω)
    exact (mul_nonneg_iff_of_pos_left hp).mp hpz_nonneg
  have hterm_le : ∀ Ω, Real.sqrt (p⁻¹ * g Ω) ≤ Real.sqrt (z Ω + 1) := by
    intro Ω
    have hpinv_mul_le : p⁻¹ * g Ω ≤ z Ω + 1 := by
      have hscaled := mul_le_mul_of_nonneg_left (hbound Ω) (inv_nonneg.mpr hp0)
      have hleft : p⁻¹ * g Ω ≤ p⁻¹ * (p * (z Ω + 1)) := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using hscaled
      have hright : p⁻¹ * (p * (z Ω + 1)) = z Ω + 1 := by
        field_simp [hp.ne']
      exact le_trans hleft (le_of_eq hright)
    exact Real.sqrt_le_sqrt hpinv_mul_le
  unfold bernoulliExpectation
  calc
    ∑ Ω : Finset (Fin n₁ × Fin n₂),
        bernoulliObservationWeight p Ω * Real.sqrt (p⁻¹ * g Ω)
        ≤ ∑ Ω : Finset (Fin n₁ × Fin n₂), w Ω * Real.sqrt (z Ω + 1) := by
          refine Finset.sum_le_sum ?_
          intro Ω _
          exact mul_le_mul_of_nonneg_left (hterm_le Ω) (by simpa [w] using hw Ω)
    _ ≤ Real.sqrt ((∑ Ω : Finset (Fin n₁ × Fin n₂), w Ω) *
          (∑ Ω : Finset (Fin n₁ × Fin n₂), w Ω * (z Ω + 1))) := by
          have hprod_nonneg :
              ∀ Ω : Finset (Fin n₁ × Fin n₂), 0 ≤ w Ω * (z Ω + 1) := by
            intro Ω
            exact mul_nonneg (hw Ω) (hnonneg_z1 Ω)
          have hpoint :
              ∀ Ω : Finset (Fin n₁ × Fin n₂),
                w Ω * Real.sqrt (z Ω + 1) =
                  Real.sqrt (w Ω) * Real.sqrt (w Ω * (z Ω + 1)) := by
            intro Ω
            have hs : Real.sqrt (w Ω) * Real.sqrt (w Ω) = w Ω := by
              rw [← pow_two, Real.sq_sqrt (hw Ω)]
            calc
              w Ω * Real.sqrt (z Ω + 1)
                  = (Real.sqrt (w Ω) * Real.sqrt (w Ω)) * Real.sqrt (z Ω + 1) := by
                    rw [hs]
              _ = Real.sqrt (w Ω) * (Real.sqrt (w Ω) * Real.sqrt (z Ω + 1)) := by
                    ring
              _ = Real.sqrt (w Ω) * Real.sqrt (w Ω * (z Ω + 1)) := by
                    rw [Real.sqrt_mul (hw Ω)]
          calc
            ∑ Ω : Finset (Fin n₁ × Fin n₂), w Ω * Real.sqrt (z Ω + 1)
                = ∑ Ω : Finset (Fin n₁ × Fin n₂),
                    Real.sqrt (w Ω) * Real.sqrt (w Ω * (z Ω + 1)) := by
                  apply Finset.sum_congr rfl
                  intro Ω _
                  exact hpoint Ω
            _ ≤ Real.sqrt (∑ Ω : Finset (Fin n₁ × Fin n₂), w Ω) *
                  Real.sqrt (∑ Ω : Finset (Fin n₁ × Fin n₂), w Ω * (z Ω + 1)) := by
                  simpa using
                    (Real.sum_sqrt_mul_sqrt_le
                      (s := (Finset.univ : Finset (Finset (Fin n₁ × Fin n₂))))
                      (f := w) (g := fun Ω => w Ω * (z Ω + 1)) hw hprod_nonneg)
            _ = Real.sqrt ((∑ Ω : Finset (Fin n₁ × Fin n₂), w Ω) *
                  (∑ Ω : Finset (Fin n₁ × Fin n₂), w Ω * (z Ω + 1))) := by
                  rw [Real.sqrt_mul (Finset.sum_nonneg fun Ω _ => hw Ω)]
    _ = Real.sqrt (bernoulliExpectation p z + 1) := by
          have hsum_expand :
              (∑ Ω : Finset (Fin n₁ × Fin n₂), w Ω * (z Ω + 1)) =
                bernoulliExpectation p z + 1 := by
            calc
              (∑ Ω : Finset (Fin n₁ × Fin n₂), w Ω * (z Ω + 1))
                  = (∑ Ω : Finset (Fin n₁ × Fin n₂), w Ω * z Ω) +
                      ∑ Ω : Finset (Fin n₁ × Fin n₂), w Ω := by
                    simp [mul_add, Finset.sum_add_distrib]
              _ = bernoulliExpectation p z + 1 := by
                    simp [bernoulliExpectation, w, hwsum]
          rw [hwsum, hsum_expand]
          simp
