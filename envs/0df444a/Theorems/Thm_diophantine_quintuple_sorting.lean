-- Prove2me | Theorems.Thm_diophantine_quintuple_sorting
-- name    : diophantine_quintuple_sorting
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-07T02:46:52.948596+00:00
-- url     : https://prove2.me/theorems/727c9e66-62ac-4550-bffa-6c9d9b4cb49c
-- title:
--   Increasing relabelling of a Diophantine quintuple
-- statement:
--   Let $f$ label five distinct positive integers whose pairwise products plus one are squares. Then there is an increasing labelling $g$ of the same five integers: $$g_0<g_1<g_2<g_3<g_4,$$ every value of $g$ is a value of $f$, and $g$ inherits the Diophantine property. This is the sorting step used in the proof of Theorem 1 (Section 10); it is routine combinatorics and needs no number theory.
-- source:
--   Bo He, Alain Togbé, Volker Ziegler, There is no Diophantine quintuple, arXiv:1610.04020v2, https://arxiv.org/abs/1610.04020v2; Section 10 (increasing relabelling in the proof of Theorem 1).

import Definitions.Def_diophantine_descent
set_option autoImplicit false
open DiophantineDescent

theorem diophantine_quintuple_sorting (f : Fin 5 → Nat) (hq : Quintuple f) :
    ∃ g : Fin 5 → Nat, Quintuple g ∧ Ordered g ∧ (∀ i, ∃ j, g i = f j) := by sorry
