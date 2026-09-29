-- Prove2me | Theorems.Thm_mme_Fin5_word_difference_nonzero_in_ZMod
-- name    : mme_Fin5_word_difference_nonzero_in_ZMod
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T20:49:26.035064+00:00
-- url     : https://prove2.me/theorems/714dd5ed-f21d-4d4a-bda4-fea08d2182f2
-- title:
--   Distinct five-grade words remain distinct modulo every $p\ge5$
-- statement:
--   Let $x$ and $y$ be distinct words of length $N+1$ over the five grades $\{0,1,2,3,4\}$.  For every modulus $p\ge5$, there is a coordinate $j$ for which
--
--   $$
--   (x_j-y_j)\bmod p\ne0.
--   $$
--
--   Thus a collision between two distinct Coppersmith--Winograd grade words always yields a genuinely nonzero coefficient in the modular linear hash, provided the modulus exceeds the grade range.
-- source:
--   Elementary modular arithmetic; used in the affine-hash collision count of D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), pp. 260--261 and 267--269; https://doi.org/10.1016/S0747-7171(08)80013-2

import Mathlib

theorem mme_Fin5_word_difference_nonzero_in_ZMod
    {p N : ℕ} (hp : 5 ≤ p)
    (x y : Fin (N + 1) → Fin 5) (hxy : x ≠ y) :
    ∃ j : Fin (N + 1),
      ((x j).val : ZMod p) - ((y j).val : ZMod p) ≠ 0 := by
  sorry
