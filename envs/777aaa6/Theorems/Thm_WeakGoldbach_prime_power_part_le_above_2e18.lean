-- Prove2me | Theorems.Thm_WeakGoldbach_prime_power_part_le_above_2e18
-- name    : WeakGoldbach.prime_power_part_le_above_2e18
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-12T00:57:53.801712+00:00
-- url     : https://prove2.me/theorems/a12aaff5-a053-4fc6-880a-2a4c741b84a2
-- title:
--   Prime-power correction is small for $m > 2\cdot 10^{18}$
-- statement:
--   For every natural number $m > 2\cdot 10^{18}$, the part of the weighted symmetric-offset sum coming from offsets where at least one of $m-t$, $m+t$ is a proper prime power (rather than prime) satisfies
--
--   $$
--   \sum_{\substack{0 \le t \le m-2 \\ \text{not both prime}}} \Lambda(m-t)\,\Lambda(m+t)
--   \;\le\; \tfrac{1}{10}\,\mathfrak{S}(2m)\,m.
--   $$
--
--   This is elementary: proper prime powers below $2m$ number $O(\sqrt m \log_2 m)$ and each term is at most $\log^2(2m)$, so the sum is $O(\sqrt m\,\mathrm{polylog}\, m)$ — dwarfed by the linear main term. It is the standard ``remove the prime powers'' step that passes from the weighted circle-method count to the genuine prime-pair count.
-- source:
--   Standard elementary estimate; Vaughan, The Hardy-Littlewood Method

import Mathlib

namespace WeakGoldbach

theorem prime_power_part_le_above_2e18 (m : ℕ) (hm : 2 * 10 ^ 18 < m) :
    ∑ t ∈ (Finset.range (m - 1)).filter
        (fun t => ¬ (Nat.Prime (m - t) ∧ Nat.Prime (m + t))),
      (ArithmeticFunction.vonMangoldt (m - t) : ℝ)
        * (ArithmeticFunction.vonMangoldt (m + t) : ℝ)
      ≤ (∏ p ∈ (2 * m).primeFactors.filter (2 < ·), ((p : ℝ) - 1) / ((p : ℝ) - 2))
          * (m : ℝ) * (1 / 10) := by
  sorry

end WeakGoldbach
