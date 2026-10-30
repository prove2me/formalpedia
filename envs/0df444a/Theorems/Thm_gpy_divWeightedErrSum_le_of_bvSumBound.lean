-- Prove2me | Theorems.Thm_gpy_divWeightedErrSum_le_of_bvSumBound
-- name    : gpy_divWeightedErrSum_le_of_bvSumBound
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T22:35:39.797352+00:00
-- url     : https://prove2.me/theorems/3da4ad6b-c27e-43bd-ad94-8aa67e806056
-- title:
--   Divisor-weighted error sum bounded by the sup weight times a BV sum bound
-- statement:
--   Let $M$ be a model for prime counts in arithmetic progressions, let $Y'$ be a height, and let $R$ be a level with $R^2 < (Y')^{1/2 - \eta}$ for a parameter $\eta$. Let the divisor-weighted error sum be $\sum_{L \leq R^2} \tau_{k+1}(L)^2 \cdot \text{err}(Y', L)$, where $\tau_{k+1}(L)$ counts ordered factorizations of $L$ into $k+1$ positive factors and $\text{err}(Y', L)$ is the max coprime-residue error. Suppose that for every coprime residue system $v$, the BV-type sum $\sum_q |\pi(Y'; q, v_q) - M(Y', q)|$ over moduli $q$ in the BV range is at most $B$, and that the weight $\tau_{k+1}(L)^2$ is at most $W \geq 0$ for $L \leq R^2$. Then\n\n$$\sum_{L \leq R^2} \tau_{k+1}(L)^2 \cdot \text{err}(Y', L) \leq W \cdot B.$$\n\nThe BV sum bound controls the unweighted max-error sum over $L \leq R^2$ (the $L = 0$ term vanishes, and every $1 \leq L \leq R^2$ lies in the BV range), so the sup-factor bound applies — again with the sup factor $W$ as the obstruction. Formalization Note: the divisor count, the max coprime-residue error, and the prime count in a residue class are unfolded into explicit finite sums, filters, and cardinalities.
-- source:
--   GPY divisor-weighted BV estimate: the naive sup-factor bound from a platform-shaped BV sum hypothesis, with the level constraint and the BV range

import Mathlib
open Classical

theorem gpy_divWeightedErrSum_le_of_bvSumBound {k : ℕ} (M : ℕ → ℕ → ℝ)
    (Y' R : ℕ) {η : ℝ} (B W : ℝ) (hWnn : 0 ≤ W)
    (hlev : (R : ℝ) ^ 2 < (Y' : ℝ) ^ (1 / 2 - η))
    (hBV : ∀ v : ℕ → ℕ, (∀ q, Nat.Coprime (v q) q) →
      ∑ q ∈ (Finset.range ⌈(Y' : ℝ) ^ (1 / 2 - η)⌉₊).filter
          (fun q : ℕ => 1 ≤ q ∧ (q : ℝ) < (Y' : ℝ) ^ (1 / 2 - η)),
        abs ((((Finset.range (Y' + 1)).filter
            (fun p => Nat.Prime p ∧ p ≡ v q [MOD q])).card : ℝ) - M Y' q) ≤ B)
    (hw : ∀ L ∈ Finset.range (R ^ 2 + 1),
      (((Fintype.piFinset (fun _ : Fin (k + 1) => Finset.Icc 1 L)).filter
        (fun d => ∏ i, d i = L)).card : ℝ) ^ 2 ≤ W) :
    (∑ L ∈ Finset.range (R ^ 2 + 1),
      (((Fintype.piFinset (fun _ : Fin (k + 1) => Finset.Icc 1 L)).filter
        (fun d => ∏ i, d i = L)).card : ℝ) ^ 2
        * (if hne : (((Finset.range L).filter (fun r => Nat.Coprime r L)).image
            (fun r => abs ((((Finset.range (Y' + 1)).filter
                (fun p => Nat.Prime p ∧ p ≡ r [MOD L])).card : ℝ) - M Y' L))).Nonempty
          then (((Finset.range L).filter (fun r => Nat.Coprime r L)).image
            (fun r => abs ((((Finset.range (Y' + 1)).filter
                (fun p => Nat.Prime p ∧ p ≡ r [MOD L])).card : ℝ) - M Y' L))).max' hne
          else 0)) ≤ W * B := by sorry
