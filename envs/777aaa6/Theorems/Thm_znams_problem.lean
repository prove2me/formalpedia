-- Prove2me | Theorems.Thm_znams_problem
-- name    : znams_problem
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-31T18:59:26.733021+00:00
-- url     : https://prove2.me/theorems/c3e1e438-0b1d-49b8-8cbc-7722f5c4a37f
-- statement:
--   **Znám's Problem**: For every $k \geq 2$, does there exist a set of $k$ positive integers $\{x_1, \ldots, x_k\}$ such that each $x_i$ divides $1 + \prod_{j \neq i} x_j$?
--
--   Štefan Znám posed this in 1975. Solutions are known for $k = 2, 3, \ldots, 9$. Example for $k=2$: $\{2, 3\}$ since $2 \mid 1+3=4$ and $3 \mid 1+2=3$. The question is whether solutions exist for all $k$. Closely related to Egyptian fraction representations and Sylvester sequences.
--
--   **Source**: Znám, Š. (1975). J. Number Theory 7, 303–310. Also: Sun, Z.W. (2009). On Znám's problem and generalized Znám's problem. Integers 9, A44.
-- source:
--   https://en.wikipedia.org/wiki/Zn%C3%A1m%27s_problem

import Mathlib

theorem znams_problem (k : ℕ) (hk : 2 ≤ k) :
    ∃ s : Fin k → ℕ,
      (∀ i, 0 < s i) ∧
      ∀ i, s i ∣ (1 + ∏ j ∈ Finset.univ.erase i, s j) := by
  sorry
