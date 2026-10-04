-- Prove2me | Theorems.Thm_egz_constant_sharp
-- name    : egz_constant_sharp
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T09:47:00.337747+00:00
-- url     : https://prove2.me/theorems/092fa75c-00ec-431a-83ac-044928172db7
-- title:
--   Sharpness: the Erdős–Ginzburg–Ziv constant $2n-1$ is best possible
-- statement:
--   The constant $2n - 1$ in the Erdős–Ginzburg–Ziv theorem cannot be improved: among $2n - 2$ integers, it is not always possible to find $n$ with sum divisible by $n$.
--
--   Concretely, take $n - 1$ zeros and $n - 1$ ones. Any $n$ chosen elements have sum equal to the number $j$ of chosen ones, with $0 \le j \le n - 1$. Divisibility by $n$ forces $j = 0$, i.e. all $n$ chosen elements are zeros — but only $n - 1$ zeros are available.
--
--   Together with `erdos_ginzburg_ziv`, this shows the Erdős–Ginzburg–Ziv constant of $C_n$ (the least $\ell$ such that any $\ell$ elements contain $n$ summing to zero) is exactly $2n - 1$.
--
--   **Formalization Note** The witnessing sequence is the explicit function `fun i => if (i : ℕ) < n - 1 then 1 else 0` on `Fin (2 * n - 2)`; the cardinality accounting translates the zeros block down by `n - 1` and injects it into `range (n - 1)`.
-- source:
--   Sharpness example from P. Erdos, A. Ginzburg, A. Ziv, Theorem in the additive number theory, Bull. Res. Council Israel 10F (1961), 41-43

import Mathlib

theorem egz_constant_sharp (n : ℕ) (hn : 1 < n) :
    ∃ a : Fin (2 * n - 2) → ℤ, ∀ t : Finset (Fin (2 * n - 2)), t.card = n →
      ¬ ((n : ℤ) ∣ ∑ i ∈ t, a i) := by sorry
