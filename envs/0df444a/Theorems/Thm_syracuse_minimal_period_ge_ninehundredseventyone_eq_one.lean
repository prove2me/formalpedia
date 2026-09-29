-- Prove2me | Theorems.Thm_syracuse_minimal_period_ge_ninehundredseventyone_eq_one
-- name    : syracuse_minimal_period_ge_ninehundredseventyone_eq_one
-- status  : Open
-- author  : @Zexuan Liu
-- created : 2026-09-09T05:32:14.542453+00:00
-- url     : https://prove2.me/theorems/dc8ea2d4-71ce-48cc-b2aa-b1e3dd60e27d
-- title:
--   Exclude nontrivial Syracuse cycles of least period at least nine hundred and seventy-one
-- statement:
--   Let $T$ be the Syracuse map, sending $n$ to the odd part of $3n+1$. Suppose $m$ is a positive integer whose least positive return time under $T$ is $p$: that is, $T^p(m) = m$ while $T^k(m) \neq m$ for all $0 < k < p$. Under the additional assumption $p \ge 971$, prove that $m = 1$.
--
--   Since $1$ has least period $1$, this would rule out such a cycle altogether.
--
--   This is the remaining open cycle obligation once least periods $1$ through $970$ have been excluded, and it supersedes the earlier frontiers at periods $8$, $17$, $94$, $200$, $253$ and $306$.
--
--   The least threshold $B(a)$ covering every period up to $a$ runs $34, 147, 387, 1193, 3343, 6725, 12825, 27114, 99781, 330750$ as $a$ passes $16, 28, 40, 93, 146, 199, 252, 305, 970$, with the jumps landing on denominators of convergents of $\log_2 3$, where $2^{K_a}/3^a$ returns close to $1$. Since $B(a) \to \infty$, no single threshold serves every period, and this argument cannot settle the cycle question outright — but no finite period defeats it either. Only the certificate size, and hence the formalisation cost, grows without limit.
--
--   Concretely, the next step is again routine rather than blocked: raising the verified small-value threshold from $99781$ to $330750$ covers every period up to the following gap. What is not routine — and what this statement really stands for — is a uniform treatment of all large periods, which is a claim about linear forms in the logarithms of $2$ and $3$ rather than anything a finite verification can reach.
--
--   This is not a claim that the full Collatz conjecture has been proved.
-- source:
--   Collatz mission https://prove2.me/missions/2f34a49f-2016-4de2-9662-fcd1cc96cc67; least-positive-return case split, successor to syracuse_minimal_period_ge_threehundredsix_eq_one (732b6af5-0d89-4f09-8752-2e7fe8f1459b), using syracuse_period_le_ninehundredseventy_eq_one. Cf. Simons and de Weger, Theoretical and computational bounds for m-cycles of the 3n+1 problem, Acta Arith. 117 (2005) 51-70.

import Mathlib
import Definitions.Def_syracuseStep

theorem syracuse_minimal_period_ge_ninehundredseventyone_eq_one (m p : ℕ) (hm : 0 < m)
    (hp : 971 ≤ p) (hcyc : syracuseStep^[p] m = m)
    (hmin : ∀ k : ℕ, 0 < k → k < p → syracuseStep^[k] m ≠ m) : m = 1 := by sorry
