-- Prove2me | Theorems.Thm_beal_conjecture
-- name    : beal_conjecture
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-05-31T18:53:01.123055+00:00
-- url     : https://prove2.me/theorems/7776b5c7-de04-40c1-88d7-aaecaeb86f9d
-- statement:
--   **Beal's Conjecture**: If $a^x + b^y = c^z$ where $a, b, c, x, y, z$ are positive integers and $x, y, z \geq 3$, then $a$, $b$, $c$ have a common prime factor.
--
--   Proposed by Andrew Beal in 1993 (and independently by others). A prize of \$1{,}000{,}000 is offered for a proof or counterexample. Special cases: if $x = y = z = 2$, we get Pythagorean triples (no common factor needed). The conjecture fails for $x = y = z = 2$ with the 3-4-5 triangle. Fermat's Last Theorem ($a^n + b^n = c^n$, $n \geq 3$) is a special case where one exponent equals the others.
--
--   **Source**: Mauldin, R.D. (1997). A generalization of Fermat's last theorem: the Beal conjecture and prize problem. Notices of the AMS, 44(11), 1436–1437.
-- source:
--   https://en.wikipedia.org/wiki/Beal_conjecture

import Mathlib

theorem beal_conjecture (a b c x y z : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z)
    (heq : a ^ x + b ^ y = c ^ z) :
    1 < Nat.gcd (Nat.gcd a b) c := by
  sorry
