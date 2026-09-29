-- Prove2me | Theorems.Thm_syracuse_minimal_period_ge_threehundredsix_eq_one
-- name    : syracuse_minimal_period_ge_threehundredsix_eq_one
-- status  : Open
-- author  : @Zexuan Liu
-- created : 2026-09-09T04:20:25.54722+00:00
-- url     : https://prove2.me/theorems/732b6af5-0d89-4f09-8752-2e7fe8f1459b
-- title:
--   Exclude nontrivial Syracuse cycles of least period at least three hundred and six
-- statement:
--   Let $T$ be the Syracuse map, sending $n$ to the odd part of $3n+1$. Suppose $m$ is a positive integer whose least positive return time under $T$ is $p$: that is, $T^p(m) = m$ while $T^k(m) \neq m$ for all $0 < k < p$. Under the additional assumption $p \ge 306$, prove that $m = 1$.
--
--   Since $1$ has least period $1$, this would rule out such a cycle altogether.
--
--   This is the remaining open cycle obligation once least periods $1$ through $305$ have been excluded, and it supersedes the earlier frontiers at periods $8$, $17$, $94$ and $200$.
--
--   The required threshold grows with the period: covering every period up to $a$ needs $B$ at least $34, 147, 387, 1193, 3343, 6725, 12825, 27114, 99781$ as $a$ passes $16, 28, 40, 93, 146, 199, 252, 305$. The jumps occur at denominators of convergents of $\log_2 3$, where $2^{K_a}/3^a$ approaches $1$. No single $B$ serves every period, so this line of argument cannot exclude all cycles; but there is no finite period at which it fails outright — only a threshold, and hence a formalisation cost, that grows without bound.
--
--   Concretely, period $306$ itself is reachable by the same method: it needs the small-value threshold raised from $27114$ to $99781$, a verification roughly four times the size of the present one. What no amount of such work reaches is a uniform statement over all periods, which is a claim about linear forms in the logarithms of $2$ and $3$.
--
--   This is not a claim that the full Collatz conjecture has been proved.
-- source:
--   Collatz mission https://prove2.me/missions/2f34a49f-2016-4de2-9662-fcd1cc96cc67; least-positive-return case split, successor to syracuse_minimal_period_ge_twohundred_eq_one (16e709ee-d544-4a97-b014-3b104dd36574), using syracuse_period_le_threehundredfive_eq_one. Cf. Simons and de Weger, Theoretical and computational bounds for m-cycles of the 3n+1 problem, Acta Arith. 117 (2005) 51-70.

import Mathlib
import Definitions.Def_syracuseStep

theorem syracuse_minimal_period_ge_threehundredsix_eq_one (m p : ℕ) (hm : 0 < m) (hp : 306 ≤ p)
    (hcyc : syracuseStep^[p] m = m) (hmin : ∀ k : ℕ, 0 < k → k < p → syracuseStep^[k] m ≠ m) :
    m = 1 := by sorry
