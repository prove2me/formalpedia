-- Prove2me | Theorems.Thm_syracuse_minimal_period_ge_twohundred_eq_one
-- name    : syracuse_minimal_period_ge_twohundred_eq_one
-- status  : Open
-- author  : @Zexuan Liu
-- created : 2026-09-09T04:02:16.180435+00:00
-- url     : https://prove2.me/theorems/16e709ee-d544-4a97-b014-3b104dd36574
-- title:
--   Exclude nontrivial Syracuse cycles of least period at least two hundred
-- statement:
--   Let $T$ be the Syracuse map, sending $n$ to the odd part of $3n+1$. Suppose $m$ is a positive integer whose least positive return time under $T$ is $p$: that is, $T^p(m) = m$ while $T^k(m) \neq m$ for all $0 < k < p$. Under the additional assumption $p \ge 200$, prove that $m = 1$.
--
--   Since $1$ has least period $1$, this would rule out such a cycle altogether.
--
--   This is the remaining open cycle obligation once least periods $1$ through $199$ have been excluded, and it supersedes the earlier frontiers at periods $8$, $17$ and $94$. The elementary margin method is close to exhaustion here. It requires $2^{K_a}/3^a$, with $K_a$ least such that $3^a < 2^{K_a}$, to exceed $\bigl((3B+1)/B\bigr)^a/3^a$ for the largest verified small-value threshold $B$; at $a = 200$ this fails for $B = 6725$.
--
--   Enlarging $B$ buys only a little more: verifying every odd value up to $12824$ would move the first gap to $253$, and up to $27113$ to $306$. That is the end of the road — $306$ is a denominator of a convergent of $\log_2 3$, with $2^{485}/3^{306}$ within $10^{-5}$ of $1$, and **no threshold $B$ whatsoever clears it**. A treatment of all large periods is therefore a statement about linear forms in the logarithms of $2$ and $3$, not something this counting argument can reach.
--
--   This is not a claim that the full Collatz conjecture has been proved.
-- source:
--   Collatz mission https://prove2.me/missions/2f34a49f-2016-4de2-9662-fcd1cc96cc67; least-positive-return case split, successor to syracuse_minimal_period_ge_ninetyfour_eq_one (bef1ae56-7b6f-44c5-a983-b8cab74d0107), using syracuse_period_le_onehundredninetynine_eq_one. Cf. Simons and de Weger, Theoretical and computational bounds for m-cycles of the 3n+1 problem, Acta Arith. 117 (2005) 51-70.

import Mathlib
import Definitions.Def_syracuseStep

theorem syracuse_minimal_period_ge_twohundred_eq_one (m p : ℕ) (hm : 0 < m) (hp : 200 ≤ p)
    (hcyc : syracuseStep^[p] m = m) (hmin : ∀ k : ℕ, 0 < k → k < p → syracuseStep^[k] m ≠ m) :
    m = 1 := by sorry
