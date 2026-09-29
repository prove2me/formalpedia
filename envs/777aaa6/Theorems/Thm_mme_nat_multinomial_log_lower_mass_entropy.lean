-- Prove2me | Theorems.Thm_mme_nat_multinomial_log_lower_mass_entropy
-- name    : mme_nat_multinomial_log_lower_mass_entropy
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T01:17:36.729378+00:00
-- url     : https://prove2.me/theorems/69879847-c4f7-4e58-96b4-b3ba44424367
-- title:
--   Multinomial coefficient: log lower bound by mass entropy
-- statement:
--   This is the standard type-class lower bound for a multinomial coefficient, written with natural logarithms and unnormalized masses.
--
--   Let $R$ be a finite set, $w:R\to\mathbb N$, and $W=\sum_{i\in R} w_i$. Write
--
--   $$
--   \mathcal H(w)\;=\;W\log W-\sum_{i\in R} w_i\log w_i
--   $$
--
--   for the mass entropy of $w$ (with $0\log 0=0$), which equals $W\,H(w/W)$ in nats when $W>0$ and is $0$ when $W=0$.
--
--   **Claim.**
--
--   $$
--   \mathcal H(w)\;-\;|R|\,\log\bigl(6(W+1)\bigr)\;\le\;\log\frac{W!}{\prod_{i\in R} w_i!}.
--   $$
--
--   This is the case $m=1$ of the [polynomial entropy lower bound for multinomials](p2m:theorem/2e42e907-1a53-420b-910e-0dae2ae915a9), $e^{W H(w/W)}\le (6(W+1))^{|R|}\binom{W}{w}$, restated in natural logarithms; it also covers $W=0$.
--
--   **Role.** It turns a logarithm of an explicit multinomial coefficient with huge entries into an explicit entropy expression with an additive error of only $|R|\log(6(W+1))$. This is how Stirling-type estimates enter numeric dimension certificates such as the [boundary unit factor bound](p2m:theorem/1e6f06b7-d9ba-4462-af69-0d03251d1f30).
--
--   **Formalization Note.** $\mathcal H(w)$ is `MME.RegionRate.massEntropy (fun i => (w i : ℝ))`, defined as $\sum_i \mathrm{negMulLog}(w_i)-\mathrm{negMulLog}(W)$. The multinomial is the natural-number quotient `(∑ i, w i)! / ∏ i, (w i)!`, which is exact.
-- source:
--   Standard method of types bound, e.g. Cover-Thomas, Elements of Information Theory, 2nd ed., Theorem 11.1.3 (Section 11.1); here derived from the proved lemma mme_dwz_multinomial_entropy_polynomial_lower (2e42e907) with m=1.

import Theorems.Thm_mme_dwz_multinomial_entropy_polynomial_lower
import Definitions.Def_mme_regional_entropy_rate_data
open scoped BigOperators
set_option autoImplicit false

theorem mme_nat_multinomial_log_lower_mass_entropy {R : Type*} [Fintype R] (w : R → ℕ) :
    MME.RegionRate.massEntropy (fun i => (w i : ℝ)) -
        (Fintype.card R : ℝ) * Real.log (6 * (((∑ i, w i : ℕ) : ℝ) + 1)) ≤
      Real.log (((∑ i, w i).factorial / ∏ i, (w i).factorial : ℕ) : ℝ) := by sorry
