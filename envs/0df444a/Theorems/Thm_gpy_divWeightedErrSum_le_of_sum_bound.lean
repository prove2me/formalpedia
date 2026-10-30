-- Prove2me | Theorems.Thm_gpy_divWeightedErrSum_le_of_sum_bound
-- name    : gpy_divWeightedErrSum_le_of_sum_bound
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T22:31:30.72379+00:00
-- url     : https://prove2.me/theorems/5551649d-a573-4212-bb0b-25cf5b090ff4
-- title:
--   Divisor-weighted error sum bounded by the sup weight times the unweighted sum
-- statement:
--   Let $M$ be a model for prime counts in arithmetic progressions, let $Y'$ be a height, let $Q$ be a range bound, and let $k$ be a tuple dimension. Let the divisor-weighted error sum be $\sum_{L \leq Q} \tau_{k+1}(L)^2 \cdot \text{err}(Y', L)$, where $\tau_{k+1}(L)$ counts ordered factorizations of $L$ into $k+1$ positive factors and $\text{err}(Y', L)$ is the max coprime-residue error at height $Y'$ and modulus $L$. Suppose the weight $\tau_{k+1}(L)^2$ is at most $W$ throughout the range, with $W \geq 0$, and the unweighted max-error sum $\sum_{L \leq Q} \text{err}(Y', L)$ is at most $B$. Then\n\n$$\sum_{L \leq Q} \tau_{k+1}(L)^2 \cdot \text{err}(Y', L) \leq W \cdot B.$$\n\nThis is precisely what the plain BV record buys, and no more: the factor $W = \sup_{L \leq Q} \tau_{k+1}(L)^2$ is the whole obstruction, since it is super-polylogarithmic at primorial-type moduli and is not absorbed by re-choosing a logarithmic exponent. Formalization Note: the divisor count and the max coprime-residue error are unfolded into explicit finite sums, filters, and cardinalities.
-- source:
--   GPY divisor-weighted BV estimate: the naive sup-factor bound, if the weight is at most W on the range and the unweighted max-error sum is at most B, then the divisor-weighted sum is at most W times B

import Mathlib
open Classical

theorem gpy_divWeightedErrSum_le_of_sum_bound {k : ℕ} (M : ℕ → ℕ → ℝ)
    (Y' Q : ℕ) {W B : ℝ} (hWnn : 0 ≤ W)
    (hw : ∀ L ∈ Finset.range (Q + 1),
      (((Fintype.piFinset (fun _ : Fin (k + 1) => Finset.Icc 1 L)).filter
        (fun d => ∏ i, d i = L)).card : ℝ) ^ 2 ≤ W)
    (hsum : ∑ L ∈ Finset.range (Q + 1),
      (if hne : (((Finset.range L).filter (fun r => Nat.Coprime r L)).image
          (fun r => abs ((((Finset.range (Y' + 1)).filter
              (fun p => Nat.Prime p ∧ p ≡ r [MOD L])).card : ℝ) - M Y' L))).Nonempty
        then (((Finset.range L).filter (fun r => Nat.Coprime r L)).image
          (fun r => abs ((((Finset.range (Y' + 1)).filter
              (fun p => Nat.Prime p ∧ p ≡ r [MOD L])).card : ℝ) - M Y' L))).max' hne
        else 0) ≤ B) :
    (∑ L ∈ Finset.range (Q + 1),
      (((Fintype.piFinset (fun _ : Fin (k + 1) => Finset.Icc 1 L)).filter
        (fun d => ∏ i, d i = L)).card : ℝ) ^ 2
        * (if hne : (((Finset.range L).filter (fun r => Nat.Coprime r L)).image
            (fun r => abs ((((Finset.range (Y' + 1)).filter
                (fun p => Nat.Prime p ∧ p ≡ r [MOD L])).card : ℝ) - M Y' L))).Nonempty
          then (((Finset.range L).filter (fun r => Nat.Coprime r L)).image
            (fun r => abs ((((Finset.range (Y' + 1)).filter
                (fun p => Nat.Prime p ∧ p ≡ r [MOD L])).card : ℝ) - M Y' L))).max' hne
          else 0)) ≤ W * B := by sorry
