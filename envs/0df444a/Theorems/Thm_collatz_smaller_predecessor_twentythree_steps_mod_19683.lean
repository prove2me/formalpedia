-- Prove2me | Theorems.Thm_collatz_smaller_predecessor_twentythree_steps_mod_19683
-- name    : collatz_smaller_predecessor_twentythree_steps_mod_19683
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-25T17:53:33.538435+00:00
-- url     : https://prove2.me/theorems/60470e3d-ef32-45f3-95f8-9ff7b26dbbe8
-- title:
--   Smaller 23-step Collatz predecessors in 32 classes modulo 19683
-- statement:
--   Let $C$ be the ordinary Collatz map. Write $C^t$ for its $t$-fold iterate, counting each odd step and each halving separately. Define the set of residues $R$ modulo $3^9=19683$ by
--
--   $$
--   R = \{154, 433, 1384, 1663, 2134, 2548, 3268, 3364, 3970, 4249, 4498, 4816, 5671, 5815, 6382, 6517, 6805, 7516, 8227, 8650, 9352, 11053, 11197, 12187, 12898, 13312, 14032, 15013, 15580, 17146, 17281, 18376\}.
--   $$
--
--   For every natural number $n$ with $nmod 19683in R$, there is a natural number $k$ satisfying
--
--   $$
--   0<k<n,qquad C^{23}(k)=n.
--   $$
--
--   These residue classes give explicit smaller starts whose orbits meet the orbit of $n$ at its initial value. Their residues modulo $3^7$ lie outside the eight previously certified eighteen-step classes.
-- source:
--   New certificates for the Collatz mission, extending the progression method of https://prove2.me/theorems/0dc7cdb4-7aac-48c4-8093-9005707e9352 and applied to https://prove2.me/theorems/be9c3278-d7aa-42c6-a8d9-c9b925b1847b.

import Definitions.Def_collatzStepMap
import Mathlib.Logic.Function.Iterate

theorem collatz_smaller_predecessor_twentythree_steps_mod_19683 (n : ℕ)
    (h : n % 19683 ∈ ([154, 433, 1384, 1663, 2134, 2548, 3268, 3364,
      3970, 4249, 4498, 4816, 5671, 5815, 6382, 6517,
      6805, 7516, 8227, 8650, 9352, 11053, 11197, 12187,
      12898, 13312, 14032, 15013, 15580, 17146, 17281, 18376] : List ℕ)) :
    ∃ k : ℕ, 0 < k ∧ k < n ∧ collatzStep^[23] k = n := by sorry
