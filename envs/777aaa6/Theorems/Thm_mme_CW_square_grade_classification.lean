-- Prove2me | Theorems.Thm_mme_CW_square_grade_classification
-- name    : mme_CW_square_grade_classification
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T04:45:36.048575+00:00
-- url     : https://prove2.me/theorems/e466c9ad-dcfd-4252-af18-cdd55de391e4
-- title:
--   Classification of the fifteen CW tensor-square grades
-- statement:
--   Let $I,J,K\in\{0,1,2,3,4\}$ be the three regrouped grades of a block in the square of the Coppersmith--Winograd tensor. If $I+J+K=4$, then $(I,J,K)$ is one of exactly fifteen ordered triples. Equivalently, it belongs to one of four cyclic shapes: $(0,0,4)$, $(0,1,3)$, $(0,2,2)$, or $(1,1,2)$.
--
--   This finite classification turns the grade-sum invariant from equation (11) into the four constituent classes analyzed on journal pp. 266--267.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), equation (11) and the four tensor-square constituent classes on journal pp. 265--267 (PDF pp. 15--17); https://www.sciencedirect.com/science/article/pii/S0747717108800132

import Mathlib.Tactic

theorem mme_CW_square_grade_classification
    (I J K : Fin 5)
    (hsum : I.val + J.val + K.val = 4) :
    (I, J, K) = (0, 0, 4) ∨
    (I, J, K) = (0, 1, 3) ∨
    (I, J, K) = (0, 2, 2) ∨
    (I, J, K) = (0, 3, 1) ∨
    (I, J, K) = (0, 4, 0) ∨
    (I, J, K) = (1, 0, 3) ∨
    (I, J, K) = (1, 1, 2) ∨
    (I, J, K) = (1, 2, 1) ∨
    (I, J, K) = (1, 3, 0) ∨
    (I, J, K) = (2, 0, 2) ∨
    (I, J, K) = (2, 1, 1) ∨
    (I, J, K) = (2, 2, 0) ∨
    (I, J, K) = (3, 0, 1) ∨
    (I, J, K) = (3, 1, 0) ∨
    (I, J, K) = (4, 0, 0) := by sorry
