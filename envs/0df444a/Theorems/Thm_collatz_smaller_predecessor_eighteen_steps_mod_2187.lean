-- Prove2me | Theorems.Thm_collatz_smaller_predecessor_eighteen_steps_mod_2187
-- name    : collatz_smaller_predecessor_eighteen_steps_mod_2187
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-24T07:21:47.332847+00:00
-- url     : https://prove2.me/theorems/0dc7cdb4-7aac-48c4-8093-9005707e9352
-- title:
--   Smaller Collatz predecessors in eighteen steps on eight classes modulo 2187
-- statement:
--   Let $C$ be the ordinary Collatz map, with an odd step and the following halving counted separately. For every natural number $n$ whose residue modulo $2187=3^7$ lies in
--   $$R=\{205,325,919,991,1000,1090,1171,2170\},$$
--   there is a positive $k<n$ with $C^{18}(k)=n$.
--
--   More explicitly, write $n=2187q+r$ in one of these eight classes and take $k=2048q+s$. In the displayed order of $r$, the corresponding values of $s$ are $191,303,859,927,935,1019,1095,2031$. The eighteen steps contain seven odd steps and eleven halvings.
-- source:
--   Original eighteen-step inverse path certificates for the bounded inverse-search branch of https://prove2.me/theorems/3c628eed-a5a7-46d4-b122-633ac4d29a8f. For the inverse-tree method see D. Applegate and J. C. Lagarias, Lower bounds for the total stopping time of 3X+1 iterates, section 2, https://arxiv.org/abs/math/0103054.

import Definitions.Def_collatzStepMap
import Mathlib.Logic.Function.Iterate

theorem collatz_smaller_predecessor_eighteen_steps_mod_2187 (n : ℕ)
    (h : n % 2187 ∈ [205, 325, 919, 991, 1000, 1090, 1171, 2170]) :
    ∃ k : ℕ, 0 < k ∧ k < n ∧ collatzStep^[18] k = n := by sorry
