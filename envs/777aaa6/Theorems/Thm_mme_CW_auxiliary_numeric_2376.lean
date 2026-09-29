-- Prove2me | Theorems.Thm_mme_CW_auxiliary_numeric_2376
-- name    : mme_CW_auxiliary_numeric_2376
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-23T23:25:16.888059+00:00
-- url     : https://prove2.me/theorems/70666288-d7ee-49ce-9d56-e30d68ab53dd
-- title:
--   Exact numerical certificate at the Coppersmith--Winograd 2.376 endpoint
-- statement:
--   At $q=6$ and $\tau=99/125$, take the exact rational parameters $$a=\frac{233}{10^6},\quad b=\frac{12506}{10^6},\quad c=\frac{102546}{10^6},\quad d=\frac{616627}{3\cdot10^6}.$$ Then the normalized right-hand side of the Section 8 auxiliary equation is strictly larger than $64=(q+2)^2$. Written out exactly, the theorem certifies the same five real-power numerator and denominator factors displayed on journal p. 269. The parameter $d$ enforces $3a+6b+3c+3d=1$ exactly and rounds to the source decimal $0.205542$. This strict inequality is the numerical half of $\omega<2.376$; it contains no floating-point premise.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), normalized auxiliary equation and numerical parameters, journal p. 269 (PDF p. 19); https://www.sciencedirect.com/science/article/pii/S0747717108800132

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real

theorem mme_CW_auxiliary_numeric_2376 :
    (64 : ℝ) <
      (12 : ℝ) ^ (6 * (99 / 125 : ℝ) * (12506 / 1000000 : ℝ)) *
          (38 : ℝ) ^ (3 * (99 / 125 : ℝ) * (102546 / 1000000 : ℝ)) *
          (4 * (6 : ℝ) ^ (3 * (99 / 125 : ℝ)) *
            ((6 : ℝ) ^ (3 * (99 / 125 : ℝ)) + 2)) ^ (616627 / (3 * 1000000) : ℝ) /
        ((2 * (233 / 1000000 : ℝ) + 2 * (12506 / 1000000 : ℝ) +
              (102546 / 1000000 : ℝ)) ^
            (2 * (233 / 1000000 : ℝ) + 2 * (12506 / 1000000 : ℝ) +
              (102546 / 1000000 : ℝ)) *
          (2 * (12506 / 1000000 : ℝ) + 2 * (616627 / (3 * 1000000) : ℝ)) ^
            (2 * (12506 / 1000000 : ℝ) + 2 * (616627 / (3 * 1000000) : ℝ)) *
          (2 * (102546 / 1000000 : ℝ) + (616627 / (3 * 1000000) : ℝ)) ^
            (2 * (102546 / 1000000 : ℝ) + (616627 / (3 * 1000000) : ℝ)) *
          (2 * (12506 / 1000000 : ℝ)) ^ (2 * (12506 / 1000000 : ℝ)) *
          (233 / 1000000 : ℝ) ^ (233 / 1000000 : ℝ)) := by sorry
