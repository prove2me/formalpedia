-- Prove2me | Theorems.Thm_syracuse_minimal_period_ge_ninetyfour_eq_one
-- name    : syracuse_minimal_period_ge_ninetyfour_eq_one
-- status  : Open
-- author  : @Zexuan Liu
-- created : 2026-09-09T03:40:26.565416+00:00
-- url     : https://prove2.me/theorems/bef1ae56-7b6f-44c5-a983-b8cab74d0107
-- title:
--   Exclude nontrivial Syracuse cycles of least period at least ninety-four
-- statement:
--   Let $T$ be the Syracuse map, sending $n$ to the odd part of $3n+1$. Suppose $m$ is a positive integer whose least positive return time under $T$ is $p$: that is, $T^p(m) = m$ while $T^k(m) \neq m$ for all $0 < k < p$. Under the additional assumption $p \ge 94$, prove that $m = 1$.
--
--   Since $1$ has least period $1$, this would rule out such a cycle altogether.
--
--   This is the remaining open cycle obligation once least periods $1$ through $93$ have been excluded, and it supersedes the earlier frontiers at periods $8$ and $17$. The elementary margin method stops here. It requires $2^{K_a}/3^a$ (with $K_a$ least such that $3^a < 2^{K_a}$) to exceed $\bigl((3B+1)/B\bigr)^a/3^a$ for the largest verified small-value threshold $B$, and at $a = 94$ this fails for $B = 1193$. Enlarging $B$ buys only finitely much more ground: verifying every odd value up to $3342$ would move the first gap to $147$, up to $6724$ to $200$, and up to $27113$ to $306$ — and $306$, a denominator of a convergent of $\log_2 3$, is where the approach is defeated outright, because $2^{485}/3^{306}$ is within $10^{-5}$ of $1$.
--
--   A treatment of all large periods is therefore a statement about linear forms in the logarithms of $2$ and $3$, not something the counting argument can reach. This is not a claim that the full Collatz conjecture has been proved.
-- source:
--   Collatz mission https://prove2.me/missions/2f34a49f-2016-4de2-9662-fcd1cc96cc67; least-positive-return case split, successor to syracuse_minimal_period_ge_seventeen_eq_one (dbb30e5a-da29-4522-a4b6-055020fc4e5a), using syracuse_period_le_ninetythree_eq_one. Cf. Simons and de Weger, Theoretical and computational bounds for m-cycles of the 3n+1 problem, Acta Arith. 117 (2005) 51-70.

import Mathlib
import Definitions.Def_syracuseStep

theorem syracuse_minimal_period_ge_ninetyfour_eq_one (m p : ℕ) (hm : 0 < m) (hp : 94 ≤ p)
    (hcyc : syracuseStep^[p] m = m) (hmin : ∀ k : ℕ, 0 < k → k < p → syracuseStep^[k] m ≠ m) :
    m = 1 := by sorry
