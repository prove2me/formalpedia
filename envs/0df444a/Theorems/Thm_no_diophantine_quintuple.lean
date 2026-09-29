-- Prove2me | Theorems.Thm_no_diophantine_quintuple
-- name    : no_diophantine_quintuple
-- status  : Open
-- author  : @xuanji
-- created : 2026-09-07T01:02:55.457975+00:00
-- url     : https://prove2.me/theorems/780bea2d-21a2-4653-82ae-842b3c4a1927
-- title:
--   There is no Diophantine quintuple
-- statement:
--   A Diophantine $m$-tuple is a set of $m$ distinct positive integers such that the product of any two different elements, increased by one, is a perfect square. There is no Diophantine quintuple: there do not exist five distinct positive integers $a_1,\ldots,a_5$ satisfying
--
--   $$
--   a_i a_j+1\text{ is a perfect square for every }1\le i<j\le5.
--   $$
--
--   This is Theorem 1 of Bo He, Alain Togbé, and Volker Ziegler, *There is no Diophantine quintuple*. It settles the Diophantine quintuple conjecture. The result is proved in the cited paper; the task here is to formalize it in Lean.
-- source:
--   Bo He, Alain Togbé, and Volker Ziegler, There is no Diophantine quintuple, arXiv:1610.04020v2 (26 March 2018), Section 1, Theorem 1. https://arxiv.org/abs/1610.04020v2

import Init
set_option autoImplicit false

theorem no_diophantine_quintuple :
    ¬ ∃ a : Fin 5 → Nat,
      (∀ i, 0 < a i) ∧
      (∀ i j, i ≠ j → a i ≠ a j) ∧
      (∀ i j, i ≠ j → ∃ r : Nat, a i * a j + 1 = r ^ 2) := by sorry
