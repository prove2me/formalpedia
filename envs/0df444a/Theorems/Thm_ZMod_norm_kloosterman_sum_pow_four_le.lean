-- Prove2me | Theorems.Thm_ZMod_norm_kloosterman_sum_pow_four_le
-- name    : ZMod.norm_kloosterman_sum_pow_four_le
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-13T23:25:08.490348+00:00
-- url     : https://prove2.me/theorems/7d546b74-b761-4ada-9f72-c92d1be5ab6e
-- title:
--   Kloosterman's bound: $|S(m,r;p)|^4 \le 3p^3$ for Kloosterman sums modulo a prime
-- statement:
--   Let $p$ be a prime and let $m, r \in \mathbb F_p$ be nonzero. The Kloosterman sum
--
--   $$S(m,r;p) = \sum_{x \in \mathbb F_p^\times} e\!\left(\frac{m x + r \bar x}{p}\right), \qquad e(t) = e^{2\pi i t},$$
--
--   where $\bar x$ is the inverse of $x$ modulo $p$, satisfies
--
--   $$|S(m,r;p)|^4 \le 3p^3, \qquad\text{so}\qquad |S(m,r;p)| \le 3^{1/4}\, p^{3/4}.$$
--
--   Role: this is Kloosterman's 1926 estimate, the first bound for Kloosterman sums that beats the trivial bound $|S(m,r;p)| \le p - 1$ by a power of $p$. Bounds of this kind make $\sum_c |S(m,n;c)|\,c^{-2}$ converge, which is what weight-2 Poincaré series and the Petersson formula need. Weil (1948) later improved the exponent to $|S(m,r;p)| \le 2\sqrt p$.
--
--   **Formalization Note**: `ZMod.stdAddChar` is Mathlib's standard additive character of `ZMod p`, $t \mapsto e^{2\pi i t/p}$, so the summand is $e((m x + r \bar x)/p)$. The sum runs over the unit group `(ZMod p)ˣ`, and `(x : ZMod p)⁻¹` is the inverse in the field `ZMod p`. The bound is stated for the fourth power, which avoids real exponents.
-- source:
--   H. D. Kloosterman, On the representation of numbers in the form ax^2 + by^2 + cz^2 + dt^2, Acta Mathematica 49 (1926), 407-464

import Mathlib

set_option autoImplicit false

theorem ZMod.norm_kloosterman_sum_pow_four_le (p : ℕ) [Fact p.Prime] {m r : ZMod p}
    (hm : m ≠ 0) (hr : r ≠ 0) :
    ‖∑ x : (ZMod p)ˣ, ZMod.stdAddChar (m * (x : ZMod p) + r * (x : ZMod p)⁻¹)‖ ^ 4 ≤
      3 * (p : ℝ) ^ 3 := by sorry
