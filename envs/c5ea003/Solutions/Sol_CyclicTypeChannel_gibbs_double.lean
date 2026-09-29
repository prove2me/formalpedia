-- Prove2me | solution 1 for CyclicTypeChannel.gibbs_double
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T22:25:16.834756+00:00
-- url     : https://prove2.me/submissions/7cf79fe5-53d0-4f75-8f2a-264fb61dfce0

-- Sol generated from Shared/CyclicTypeChannelNonneg.lean
import Mathlib
import Definitions.Def_Shared_CyclicTypeChannel
import Theorems.Thm_CyclicTypeChannel_gibbs_term
/-
# Non-negativity of the counting mutual information

The channel quantities used for the cyclic splitting-type channel are honest
information-theoretic objects: this file proves the Gibbs inequality for the
counting framework, i.e. `I(g ; k) ≥ 0` for every pair of read-outs of a finite
uniform source, and derives the sandwich `0 ≤ I(g ; k) ≤ H(g)`.

The proof is the classical one: `I` is the Kullback–Leibler divergence between
the joint law and the product of the marginals, and `log t ≤ t - 1`.
-/

open CyclicTypeChannel

open Finset

variable {α β γ : Type*} [DecidableEq β] [DecidableEq γ]

/-! ## 1. The analytic core -/



/-! ## 2. The joint count array of two read-outs -/


variable (s : Finset α) (g : α → β) (k : α → γ)







/-! ## 3. Non-negativity -/





open CyclicTypeChannel in
omit [DecidableEq β] [DecidableEq γ] in
theorem solution(C : Finset γ) (T : Finset β) (N : ℝ) (hN : 0 < N)
    (n : γ → β → ℝ) (m : β → ℝ) (M : γ → ℝ)
    (hn : ∀ c v, 0 ≤ n c v) (hm : ∀ v ∈ T, 0 < m v) (hM : ∀ c ∈ C, 0 < M c)
    (hsm : ∑ v ∈ T, m v = N) (hsM : ∑ c ∈ C, M c = N)
    (hnv : ∀ c ∈ C, ∑ v ∈ T, n c v = M c) :
    0 ≤ ∑ c ∈ C, ∑ v ∈ T,
      (n c v / N) *
        (Real.logb 2 N - Real.logb 2 (m v) - Real.logb 2 (M c) + Real.logb 2 (n c v)) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  -- term-wise Gibbs bound
  have key : ∀ c ∈ C, ∀ v ∈ T,
      (n c v / N - m v * M c / (N * N)) / Real.log 2
        ≤ (n c v / N) *
          (Real.logb 2 N - Real.logb 2 (m v) - Real.logb 2 (M c) + Real.logb 2 (n c v)) := by
    intro c hc v hv
    have hmv : 0 < m v := hm v hv
    have hMc : 0 < M c := hM c hc
    have hq : 0 ≤ n c v / N := div_nonneg (hn c v) hN.le
    have hppos : 0 < m v * M c / (N * N) := div_pos (mul_pos hmv hMc) (mul_pos hN hN)
    refine le_trans (gibbs_term hq hppos.le (fun _ => hppos)) (le_of_eq ?_)
    rcases (hn c v).eq_or_lt with h0 | h0
    · rw [← h0]
      simp
    · have hEq : (n c v / N) / (m v * M c / (N * N)) = n c v * N / (m v * M c) := by
        field_simp
      rw [hEq, Real.logb_div (by positivity) (by positivity),
        Real.logb_mul (ne_of_gt h0) (ne_of_gt hN), Real.logb_mul (ne_of_gt hmv) (ne_of_gt hMc)]
      ring
  refine le_trans ?_ (Finset.sum_le_sum fun c hc => Finset.sum_le_sum (key c hc))
  -- the lower bound telescopes to zero
  have h1 : ∑ c ∈ C, ∑ v ∈ T, n c v / N = 1 := by
    have hstep : ∑ c ∈ C, ∑ v ∈ T, n c v / N = (∑ c ∈ C, ∑ v ∈ T, n c v) / N := by
      simp only [← Finset.sum_div]
    rw [hstep, Finset.sum_congr rfl hnv, hsM, div_self (ne_of_gt hN)]
  have h2 : ∑ c ∈ C, ∑ v ∈ T, m v * M c / (N * N) = 1 := by
    have hstep : ∑ c ∈ C, ∑ v ∈ T, m v * M c / (N * N)
        = ((∑ v ∈ T, m v) * (∑ c ∈ C, M c)) / (N * N) := by
      rw [Finset.sum_mul, Finset.sum_div, Finset.sum_comm]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [Finset.mul_sum, Finset.sum_div]
    rw [hstep, hsm, hsM, div_self (by positivity)]
  have hzero : ∑ c ∈ C, ∑ v ∈ T, (n c v / N - m v * M c / (N * N)) = 0 := by
    simp only [Finset.sum_sub_distrib]
    rw [h1, h2, sub_self]
  have hcollapse : ∑ c ∈ C, ∑ v ∈ T, (n c v / N - m v * M c / (N * N)) / Real.log 2
      = (∑ c ∈ C, ∑ v ∈ T, (n c v / N - m v * M c / (N * N))) / Real.log 2 := by
    simp only [← Finset.sum_div]
  rw [hcollapse, hzero, zero_div]
