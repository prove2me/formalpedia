-- Prove2me | Theorems.Thm_mme_CW_fourth_left_grade_fiber_nonempty_iff
-- name    : mme_CW_fourth_left_grade_fiber_nonempty_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-17T08:21:16.112812+00:00
-- url     : https://prove2.me/theorems/2836ca14-5fe5-4179-88f7-fc894c425dc4
-- title:
--   Exact availability of canonical fourth-power left-grade labels
-- statement:
--   Let $q>0$. A coordinate of the Coppersmith–Winograd tensor has grade $0$, $1$, or $2$: the initial coordinate has grade $0$, the $q$ middle coordinates have grade $1$, and the terminal coordinate has grade $2$. The canonical fourth-power basis is indexed by pairs of coordinate pairs.
--
--   For a total coarse grade $k\in\{0,\ldots,8\}$ and a left-square grade $a\in\{0,\ldots,4\}$, there is a canonical basis index with these two grades if and only if
--   $$
--   a\le k\le a+4.
--   $$
--
--   Equivalently, the implied right-square grade $k-a$ must lie in $\{0,\ldots,4\}$. This identifies the actual image of the left-grade label on every canonical fourth-power coarse basis fiber, including the fibers used at $q=5$. It concerns availability of basis coordinates, not a nonzero coefficient of any specified trilinear constituent, nor a lower bound on its tensor value.
-- source:
--   Derived finite basis-availability criterion from Duan–Wu–Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section 3.5 (leveled partitions) and Section 5.1, Definitions 5.3–5.4 (small blocks and availability). https://arxiv.org/html/2210.10173v5#S5.SS1 . This explicit fourth-power coordinate criterion is not separately numbered in the paper.

import Definitions.Def_mme_stothers_fourth_data
open MME MME.StothersFourth
set_option autoImplicit false

theorem mme_CW_fourth_left_grade_fiber_nonempty_iff (q : ℕ) (hq : 0 < q)
    (k : Fin 9) (a : Fin 5) :
    (∃ x : (Fin (q + 2) × Fin (q + 2)) × (Fin (q + 2) × Fin (q + 2)),
      cwFourthPairGrade q x = k ∧ cwSquarePairGrade q x.1 = a) ↔
      a.val ≤ k.val ∧ k.val ≤ a.val + 4 := by sorry
