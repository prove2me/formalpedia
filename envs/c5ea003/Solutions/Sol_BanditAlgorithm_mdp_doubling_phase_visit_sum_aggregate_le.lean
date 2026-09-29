-- Prove2me | solution 1 for BanditAlgorithm.mdp_doubling_phase_visit_sum_aggregate_le
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-08-02T03:44:50.769715+00:00
-- url     : https://prove2.me/submissions/5ba1c325-016b-49fb-b5b0-928f42d7a98c

import Theorems.Thm_BanditAlgorithm_mdp_doubling_phase_visit_sum_le
import Mathlib.Algebra.Order.Chebyshev

/-!
# Aggregating the doubling-phase sum over all state-action pairs

Step 3 of the proof of L&S Theorem 38.6 sums the doubling bound of
Exercise 38.22 over the `SA` state-action pairs and then applies Cauchy-Schwarz
to `∑_{s,a} √(T_n(s,a))`, using `∑_{s,a} T_n(s,a) = n`:

  `∑_{s,a} ∑_{k<K} T_(k)(s,a)/√(1 ∨ T_{τ_k-1}(s,a)) ≤ (√2+1) √(SA·n)`.

The per-pair bound is imported; what is proved here is the aggregation.
-/

/-- Cauchy-Schwarz in the form used in Step 3: `∑ √(f i) ≤ √(|s| ∑ f)`. -/
theorem sum_sqrt_le_sqrt_card_mul_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) :
    ∑ i ∈ s, Real.sqrt (f i) ≤ Real.sqrt (s.card * ∑ i ∈ s, f i) := by
  have hnn : (0 : ℝ) ≤ ∑ i ∈ s, Real.sqrt (f i) :=
    Finset.sum_nonneg fun _ _ ↦ Real.sqrt_nonneg _
  have hkey : (∑ i ∈ s, Real.sqrt (f i)) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, f i := by
    refine le_trans sq_sum_le_card_mul_sum_sq ?_
    have hsq : ∑ i ∈ s, Real.sqrt (f i) ^ 2 = ∑ i ∈ s, f i :=
      Finset.sum_congr rfl fun i hi ↦ Real.sq_sqrt (hf i hi)
    rw [hsq]
  calc ∑ i ∈ s, Real.sqrt (f i)
      = Real.sqrt ((∑ i ∈ s, Real.sqrt (f i)) ^ 2) := (Real.sqrt_sq hnn).symm
    _ ≤ Real.sqrt ((s.card : ℝ) * ∑ i ∈ s, f i) := Real.sqrt_le_sqrt hkey

theorem solution {ι : Type*} [Fintype ι]
    (b c : ι → ℕ → ℝ) (n : ℝ) (K : ℕ)
    (hb0 : ∀ i, b i 0 = 0) (hc : ∀ i k, 0 ≤ c i k)
    (hstep : ∀ i k, b i (k + 1) = b i k + c i k)
    (hdouble : ∀ i k, c i k ≤ max 1 (b i k))
    (htot : ∑ i, b i K ≤ n) :
    ∑ i, ∑ k ∈ Finset.range K, c i k / Real.sqrt (max 1 (b i k))
      ≤ (Real.sqrt 2 + 1) * Real.sqrt (Fintype.card ι * n) := by
  have hbnn : ∀ i k, 0 ≤ b i k := by
    intro i k
    induction k with
    | zero => rw [hb0 i]
    | succ m ih => rw [hstep i m]; linarith [hc i m]
  have h1 : ∑ i, ∑ k ∈ Finset.range K, c i k / Real.sqrt (max 1 (b i k))
      ≤ ∑ i : ι, (Real.sqrt 2 + 1) * Real.sqrt (b i K) :=
    Finset.sum_le_sum fun i _ ↦
      BanditAlgorithm.mdp_doubling_phase_visit_sum_le (b i) (c i) (hb0 i) (hc i)
        (hstep i) (hdouble i) K
  have h2 : ∑ i : ι, Real.sqrt (b i K)
      ≤ Real.sqrt ((Fintype.card ι : ℝ) * ∑ i : ι, b i K) := by
    rw [← Finset.card_univ]
    exact sum_sqrt_le_sqrt_card_mul_sum Finset.univ (fun i ↦ b i K)
      (fun i _ ↦ hbnn i K)
  have h3 : Real.sqrt ((Fintype.card ι : ℝ) * ∑ i : ι, b i K)
      ≤ Real.sqrt ((Fintype.card ι : ℝ) * n) :=
    Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left htot (by positivity))
  have hconst : (0 : ℝ) ≤ Real.sqrt 2 + 1 := by positivity
  calc ∑ i, ∑ k ∈ Finset.range K, c i k / Real.sqrt (max 1 (b i k))
      ≤ ∑ i : ι, (Real.sqrt 2 + 1) * Real.sqrt (b i K) := h1
    _ = (Real.sqrt 2 + 1) * ∑ i : ι, Real.sqrt (b i K) := by rw [Finset.mul_sum]
    _ ≤ (Real.sqrt 2 + 1) * Real.sqrt ((Fintype.card ι : ℝ) * n) :=
        mul_le_mul_of_nonneg_left (h2.trans h3) hconst
