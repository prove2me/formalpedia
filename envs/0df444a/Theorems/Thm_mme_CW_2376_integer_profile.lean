-- Prove2me | Theorems.Thm_mme_CW_2376_integer_profile
-- name    : mme_CW_2376_integer_profile
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T04:54:19.32808+00:00
-- url     : https://prove2.me/theorems/16c6d907-669f-4526-9403-6484289f55d0
-- title:
--   Exact integer joint and marginal profile for the CW 2.376 certificate
-- statement:
--   Clear the denominators in the exact rational parameters used by the $2.376$ certificate. At scale $m$, the four joint orbit multiplicities are
--
--   $$
--   (A,B,C,D)=(699,37518,307638,616627)m,
--   $$
--
--   and their weighted total is $3A+6B+3C+3D=3{,}000{,}000m$. Equation (13) gives the five integer marginals
--
--   $$
--   (384072,1308290,1231903,75036,699)m,
--   $$
--
--   which also sum to $3{,}000{,}000m$. Thus tensor powers divisible by $3{,}000{,}000$ realize the printed profile exactly, with no frequency rounding.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), equation (13) on journal p. 268 and the numerical parameters on journal p. 269 (PDF pp. 18--19); https://www.sciencedirect.com/science/article/pii/S0747717108800132

import Mathlib.Tactic

theorem mme_CW_2376_integer_profile (m : ℕ) :
    3 * (699 * m) + 6 * (37518 * m) +
        3 * (307638 * m) + 3 * (616627 * m) = 3000000 * m ∧
    2 * (699 * m) + 2 * (37518 * m) + 307638 * m = 384072 * m ∧
    2 * (37518 * m) + 2 * (616627 * m) = 1308290 * m ∧
    2 * (307638 * m) + 616627 * m = 1231903 * m ∧
    2 * (37518 * m) = 75036 * m ∧
    699 * m = 699 * m ∧
    384072 * m + 1308290 * m + 1231903 * m +
        75036 * m + 699 * m = 3000000 * m := by sorry
