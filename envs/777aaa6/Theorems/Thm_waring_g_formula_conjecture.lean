-- Prove2me | Theorems.Thm_waring_g_formula_conjecture
-- name    : waring_g_formula_conjecture
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-05-31T19:16:23.368471+00:00
-- url     : https://prove2.me/theorems/506acc7e-2782-489d-8999-fb7291dd5e9e
-- statement:
--   **Waring's g(k) Formula Conjecture**: For all integers $k \geq 2$, the Waring function $g(k)$ — the minimum number of $k$-th powers needed to represent every positive integer — equals:
--   $$g(k) = 2^k + \left\lfloor\left(\frac{3}{2}\right)^k\right\rfloor - 2$$
--   provided $2^k \cdot \{(3/2)^k\} + \lfloor(3/2)^k\rfloor \leq 2^k - 1$ (where $\{x\}$ is the fractional part). This formula has been verified for all $k \leq 471{,}600{,}000$ (Kubina and Wunderlich, 1990). The conjecture reduces to a statement about the fractional parts of $(3/2)^k$.
--
--   **Source**: Hardy, G.H., Littlewood, J.E. (1920). Some problems of Partitio Numerorum IV. Math. Z. 12, 161–188. Mahler, K. (1957). On the fractional parts of the powers of a rational number. Mathematika 4, 122–124.
-- source:
--   https://en.wikipedia.org/wiki/Waring%27s_problem

import Mathlib

theorem waring_g_formula_conjecture (k : ℕ) (hk : 2 ≤ k)
    (hfrac : (2 : ℤ) ^ k * Int.fract ((3 / 2 : ℝ) ^ k) + ⌊(3 / 2 : ℝ) ^ k⌋ ≤ 2 ^ k - 1) :
    ∀ n : ℕ, 0 < n →
      ∃ s : Fin (2 ^ k + ⌊(3 / 2 : ℝ) ^ k⌋₊ - 2) → ℕ,
        n = ∑ i, (s i) ^ k := by
  sorry
