-- Prove2me | Theorems.Thm_flt5_5_divides_sum
-- name    : flt5_5_divides_sum
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-12T10:46:24.260774+00:00
-- url     : https://prove2.me/theorems/f3c3b1c6-6ccb-4612-b427-818acd31a007
-- statement:
--   **FLT-5 divisibility lemma.** If $a^5 + b^5 = c^5$ (integers) and $5 \mid c$, then $5 \mid a + b$. Proof: By Fermat's little theorem, $x^5 \equiv x \pmod{5}$ for all $x$, so $a + b \equiv a^5 + b^5 = c^5 \equiv 0 \pmod{5}$.

import Mathlib.Data.Int.Basic
import Mathlib.Data.ZMod.Basic

theorem flt5_5_divides_sum (a b c : ℤ) (h_eq : a ^ 5 + b ^ 5 = c ^ 5) (h5c : (5 : ℤ) ∣ c) : (5 : ℤ) ∣ a + b := by sorry
