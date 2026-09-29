-- Prove2me | solution 1 for CyclicTypeChannel.gibbs_term
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T22:23:00.806809+00:00
-- url     : https://prove2.me/submissions/30ee3854-a497-4e37-8eac-ede6f343d63b

-- Sol generated from Shared/CyclicTypeChannelNonneg.lean
import Mathlib
import Definitions.Def_Shared_CyclicTypeChannel
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
lemma solution{q p : ℝ} (hq : 0 ≤ q) (hp : 0 ≤ p) (hp' : q ≠ 0 → 0 < p) :
    (q - p) / Real.log 2 ≤ q * Real.logb 2 (q / p) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  rcases hq.eq_or_lt with h0 | h0
  · rw [← h0]
    simp only [zero_mul, zero_sub]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) hlog2.le
  · have hp0 : 0 < p := hp' (ne_of_gt h0)
    have hkey : Real.log (p / q) ≤ p / q - 1 := Real.log_le_sub_one_of_pos (by positivity)
    have hpq : Real.log (p / q) = -Real.log (q / p) := by
      rw [← Real.log_inv, inv_div]
    have h1 : q - p ≤ q * Real.log (q / p) := by
      have h2 := mul_le_mul_of_nonneg_left hkey h0.le
      rw [hpq] at h2
      have h3 : q * (p / q - 1) = p - q := by field_simp
      rw [h3] at h2
      linarith
    have hsplit : q * Real.logb 2 (q / p) = (q * Real.log (q / p)) / Real.log 2 := by
      rw [Real.logb]
      ring
    rw [hsplit]
    gcongr
