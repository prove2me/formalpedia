-- Prove2me | Theorems.Thm_collatz_coalescence_residual_fifteen_mod_sixteen_after_twentythree_step_classes
-- name    : collatz_coalescence_residual_fifteen_mod_sixteen_after_twentythree_step_classes
-- status  : Open
-- author  : @Jie Luo
-- created : 2026-11-25T17:53:31.18453+00:00
-- url     : https://prove2.me/theorems/c60a76bf-0b48-569a-b7ba-2e5b56dcecf6
-- title:
--   Remaining 15-mod-16 Collatz mergers after the 23-step certificates
-- statement:
--   Let $C$ be the ordinary Collatz map. Retain all hypotheses of the [eighteen-step residual theorem](https://prove2.me/theorems/be9c3278-d7aa-42c6-a8d9-c9b925b1847b), including its bounded-preimage condition and all its residue exclusions. Also exclude the following residues modulo $3^9=19683$.
--
--   $$
--   R = \{154, 433, 1384, 1663, 2134, 2548, 3268, 3364, 3970, 4249, 4498, 4816, 5671, 5815, 6382, 6517, 6805, 7516, 8227, 8650, 9352, 11053, 11197, 12187, 12898, 13312, 14032, 15013, 15580, 17146, 17281, 18376\}.
--   $$
--
--   If $nmod 19683
--   otin R$, prove the existence of a smaller positive start $k$ and finite indices $a,b$ such that
--
--   $$
--   0<k<n,qquad C^a(n)=C^b(k).
--   $$
--
--   This is the outstanding case after separating the classes with certified smaller 23-step predecessors.
-- source:
--   Exact complement inside https://prove2.me/theorems/be9c3278-d7aa-42c6-a8d9-c9b925b1847b after removing the 32 classes of collatz_smaller_predecessor_twentythree_steps_mod_19683.

import Definitions.Def_collatzStepMap
import Definitions.Def_collatzMinPreimage
import Mathlib.Logic.Function.Iterate

theorem collatz_coalescence_residual_fifteen_mod_sixteen_after_twentythree_step_classes (n : ℕ)
    (hlarge : 2310000 ≤ n) (hclass : n % 16 = 15)
    (hmod9 : n % 9 = 0 ∨ n % 9 = 1 ∨ n % 9 = 3 ∨ n % 9 = 6 ∨ n % 9 = 7)
    (hpreimage : ∀ t : ℕ, t ≤ 128 → n ≤ collatzMinPreimage 16 (collatzStep^[t] n))
    (h81 : n % 81 ≠ 10)
    (h2304 : n % 2304 ≠ 1743 ∧ n % 2304 ≠ 1599)
    (h4608 : n % 4608 ≠ 2847 ∧ n % 4608 ≠ 735 ∧ n % 4608 ≠ 991 ∧
      n % 4608 ≠ 2527 ∧ n % 4608 ≠ 3039 ∧ n % 4608 ≠ 4575)
    (h2187 : n % 2187 ∉ [205, 325, 919, 991, 1000, 1090, 1171, 2170])
    (h19683 : n % 19683 ∉ ([154, 433, 1384, 1663, 2134, 2548, 3268, 3364,
      3970, 4249, 4498, 4816, 5671, 5815, 6382, 6517,
      6805, 7516, 8227, 8650, 9352, 11053, 11197, 12187,
      12898, 13312, 14032, 15013, 15580, 17146, 17281, 18376] : List ℕ)) :
    ∃ k a b : ℕ, 0 < k ∧ k < n ∧ collatzStep^[a] n = collatzStep^[b] k := by
  sorry
