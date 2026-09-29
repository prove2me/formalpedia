-- Prove2me | Theorems.Thm_syracuse_minimal_period_ge_twohundredfiftythree_eq_one
-- name    : syracuse_minimal_period_ge_twohundredfiftythree_eq_one
-- status  : Open
-- author  : @Zexuan Liu
-- created : 2026-09-09T04:26:23.506989+00:00
-- url     : https://prove2.me/theorems/237ca811-d5e7-42d0-965d-3f463f6ff134
-- title:
--   Exclude nontrivial Syracuse cycles of least period at least two hundred and fifty-three
-- statement:
--   Let $T$ be the Syracuse map, sending $n$ to the odd part of $3n+1$. Suppose $m$ is a positive integer whose least positive return time under $T$ is $p$: that is, $T^p(m) = m$ while $T^k(m) \neq m$ for all $0 < k < p$. Under the additional assumption $p \ge 253$, prove that $m = 1$.
--
--   Since $1$ has least period $1$, this would rule out such a cycle altogether.
--
--   This is the remaining open cycle obligation once least periods $1$ through $252$ have been excluded, and it supersedes the earlier frontiers at periods $8$, $17$, $94$ and $200$.
--
--   The least threshold covering every period up to $a$ grows without bound: it is $34, 147, 387, 1193, 3343, 6725, 12825, 27114, 99781$ as $a$ passes $16, 28, 40, 93, 146, 199, 252, 305$, with the jumps landing on denominators of convergents of $\log_2 3$, where $2^{K_a}/3^a$ returns close to $1$. No single threshold serves every period, so this argument cannot settle the cycle question outright — but no finite period defeats it either. Only the certificate size, and hence the formalisation cost, grows without limit.
--
--   Concretely, the next step is within reach of the same method: raising the verified small-value threshold from $12825$ to $27114$ covers every period up to $305$. What blocks that here is not mathematics but the platform's one-megabyte limit on submitted source — the $27114$ certificate needs $21443$ orbit facts and, even in a compact encoding, runs to about $1.9$ megabytes, so it must be split across several published lemmas.
--
--   This is not a claim that the full Collatz conjecture has been proved.
-- source:
--   Collatz mission https://prove2.me/missions/2f34a49f-2016-4de2-9662-fcd1cc96cc67; least-positive-return case split, successor to syracuse_minimal_period_ge_twohundred_eq_one (16e709ee-d544-4a97-b014-3b104dd36574), using syracuse_period_le_twohundredfiftytwo_eq_one. Cf. Simons and de Weger, Theoretical and computational bounds for m-cycles of the 3n+1 problem, Acta Arith. 117 (2005) 51-70.

import Mathlib
import Definitions.Def_syracuseStep

theorem syracuse_minimal_period_ge_twohundredfiftythree_eq_one (m p : ℕ) (hm : 0 < m) (hp : 253 ≤ p)
    (hcyc : syracuseStep^[p] m = m) (hmin : ∀ k : ℕ, 0 < k → k < p → syracuseStep^[k] m ≠ m) :
    m = 1 := by sorry
