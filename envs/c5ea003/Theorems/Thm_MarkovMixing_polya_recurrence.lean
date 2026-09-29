-- Prove2me | Theorems.Thm_MarkovMixing_polya_recurrence
-- name    : MarkovMixing.polya_recurrence
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-22T17:41:22.02673+00:00
-- url     : https://prove2.me/theorems/0f4f862f-54d6-4174-927f-a3ea16e5d3bf
-- title:
--   Pólya's theorem
-- statement:
--   **Simple random walk on the lattice $\mathbb Z^d$** moves from a point to one of its $2d$ nearest neighbours (one coordinate changed by $\pm1$) uniformly at random. The walk is **recurrent** when return to the starting point is certain — the probability of no return by time $t$, $\mathbb P_0\{\tau^+_0>t\}$, tends to $0$ — and **transient** when with positive probability it never returns.
--
--   The theorem (**Pólya's theorem**; §21.2, Examples 21.8–21.9 of Levin–Peres–Wilmer — the capstone of Chapters 20–21) asserts:
--
--   1. in dimensions $d=1$ and $d=2$, the walk is recurrent;
--   2. in every dimension $d\ge3$, the walk is transient.
--
--   "A drunk man will find his way home, but a drunk bird may get lost forever." The dichotomy is decided by the Green's-function criterion of this mission: the return probabilities obey $P^{2t}(0,0)\asymp t^{-d/2}$ (a local central-limit estimate, by Stirling's formula in low dimension), and $\sum_tt^{-d/2}$ diverges exactly for $d\le2$. Pólya's 1921 theorem inaugurated the dimension-dependent study of random walks; formalizing the transient half in particular requires genuinely quantitative control of $d$-dimensional return probabilities.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Section 21.2, Examples 21.8-21.9 (Pólya's theorem), p. 278

import Definitions.Def_mm_countable

namespace MarkovMixing

/-- **Pólya's theorem** (LPW §21.2, Examples 21.8 and 21.9), the capstone of
Chapters 20–21: simple random walk on `ℤ^d` is recurrent in dimensions
`d ≤ 2` and transient in dimensions `d ≥ 3`. -/
theorem polya_recurrence :
    (∀ d : ℕ, 1 ≤ d → d ≤ 2 → Recurrent (srwZ d) (fun _ => 0)) ∧
    (∀ d : ℕ, 3 ≤ d → ¬Recurrent (srwZ d) (fun _ => 0)) := by
  sorry

end MarkovMixing
