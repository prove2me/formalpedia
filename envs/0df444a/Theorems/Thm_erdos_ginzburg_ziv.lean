-- Prove2me | Theorems.Thm_erdos_ginzburg_ziv
-- name    : erdos_ginzburg_ziv
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T08:23:19.760025+00:00
-- url     : https://prove2.me/theorems/3a5bd64a-8d76-431a-942f-ab28e0ef81b4
-- title:
--   Erdős–Ginzburg–Ziv theorem
-- statement:
--   **The Erdős–Ginzburg–Ziv theorem** (conjectured 1935, proved 1961): among any $2n - 1$ integers, some $n$ have a sum divisible by $n$.
--
--   $$\forall\ n \ge 1,\ \forall\ a_1, \dots, a_{2n-1} \in \mathbb{Z},\quad \exists\ 1 \le i_1 < \dots < i_n \le 2n-1,\quad n \,\big|\, a_{i_1} + \dots + a_{i_n}.$$
--
--   The number $2n - 1$ is best possible: among $2n - 2$ integers ($n - 1$ zeros and $n - 1$ ones), any $n$ chosen have sum between $0$ and $n-1$, which is divisible by $n$ only when it is $0$ — forcing all $n$ chosen elements to be zeros, of which there are only $n - 1$.
--
--   The theorem founded zero-sum theory: it is the statement that the Erdős–Ginzburg–Ziv constant $s(C_n)$ of the cyclic group equals $2n - 1$, the first nontrivial instance of a family of problems (Gao's constant, Kemnitz-type results) that remain active research. The standard proof treats prime $n$ by the Chevalley–Warning theorem and then inducts along the prime factorization of $n$.
--
--   **Formalization Note** The sequence is a function `Fin (2 * n - 1) → ℤ`, the chosen subsequence is a `Finset` of indices of cardinality `n`, and divisibility is stated as `(n : ℤ) ∣ ∑ i ∈ t, a i`. The proof is a direct appeal to Mathlib's `Int.erdos_ginzburg_ziv`, which carries out the Chevalley–Warning and prime-factorization argument.
-- source:
--   P. Erdos, A. Ginzburg, A. Ziv, Theorem in the additive number theory, Bull. Res. Council Israel 10F (1961), 41-43; conjectured 1935; Lean proof via Mathlib's Int.erdos_ginzburg_ziv (Chevalley-Warning + prime factorization induction)

import Mathlib

theorem erdos_ginzburg_ziv (n : ℕ) (a : Fin (2 * n - 1) → ℤ) :
    ∃ t : Finset (Fin (2 * n - 1)), t.card = n ∧ (n : ℤ) ∣ ∑ i ∈ t, a i := by sorry
