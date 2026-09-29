-- Prove2me | Theorems.Thm_syracuse_reaches_one_below_109781
-- name    : syracuse_reaches_one_below_109781
-- status  : Proved
-- author  : @shivm
-- created : 2026-09-09T15:19:45.18069+00:00
-- url     : https://prove2.me/theorems/ddca64a2-51c8-4a42-a481-53a1bbefe4cf
-- title:
--   Every odd $m \le 109780$ reaches $1$ under the Syracuse map
-- statement:
--   Every odd positive integer at most $109780$ reaches $1$ under the Syracuse map
--
--   $$T(n) = \frac{3n+1}{2^{\,v_2(3n+1)}},$$
--
--   the odd part of $3n+1$.
--
--   This raises the previously verified threshold `syracuse_reaches_one_below_99781` from $99780$ to $109780$. Bounds of this shape are consumed by the margin criterion `syracuse_cycle_eq_one_of_margin_at`, whose hypothesis `hsmall` asks exactly that the only Syracuse cycle meeting $[1, B)$ be $\{1\}$; raising $B$ is what raises the excludable cycle periods.
--
--   Quantitatively, the criterion needs
--
--   $$(3B+1)^a < 2^K B^a \qquad\text{whenever}\qquad 3^a < 2^K .$$
--
--   With $B = 99781$ this holds for every $a \le 970$, which is the current period frontier `syracuse_period_le_ninehundredseventy_eq_one`. The exponents at which the margin fails are the semiconvergent denominators of $\log_2 3$ — $17, 94, 200, 253, 306, 971, 1636, \dots$ — and clearing the next one, $a = 971$, requires $B \ge 330750$.
-- source:
--   Extends syracuse_reaches_one_below_99781 on the Prove2Me Collatz mission; the small-value threshold required by syracuse_cycle_eq_one_of_margin_at.

import Mathlib
import Definitions.Def_syracuseStep

theorem syracuse_reaches_one_below_109781 (m : ℕ) (hm : 0 < m) (hodd : Odd m)
    (hle : m ≤ 109780) : ∃ k : ℕ, syracuseStep^[k] m = 1 := by sorry
