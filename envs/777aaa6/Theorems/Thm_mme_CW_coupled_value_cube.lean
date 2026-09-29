-- Prove2me | Theorems.Thm_mme_CW_coupled_value_cube
-- name    : mme_CW_coupled_value_cube
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T04:30:34.762354+00:00
-- url     : https://prove2.me/theorems/0a9ce4b9-88fd-48a9-9b45-a777dd468b05
-- title:
--   Cube normalization of the coupled CW symmetric value
-- statement:
--   The cube of the symmetric-value lower bound from the coupled CW lemma is exactly its raw cyclic value:
--
--   $$
--   \left(2^{2/3}q^\tau(q^{3\tau}+2)^{1/3}\right)^3
--   =4q^{3\tau}(q^{3\tau}+2).
--   $$
--
--   This identity translates the paper's displayed symmetric value into the cubed value stored by `HasSymmetricTauValueAtLeast`.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), coupled-value conclusion on journal p. 272 (PDF p. 22); https://www.sciencedirect.com/science/article/pii/S0747717108800132

import Definitions.Def_mme_CW_coupled_value
open MME

theorem mme_CW_coupled_value_cube
    (q : ℕ) (hq : 3 ≤ q) (tau : ℝ) :
    (((2 : ℝ) ^ ((2 : ℝ) / 3) *
        (q : ℝ) ^ tau *
        (((q : ℝ) ^ (3 * tau) + 2) ^ ((1 : ℝ) / 3))) ^ (3 : ℕ)) =
      4 * (q : ℝ) ^ (3 * tau) * ((q : ℝ) ^ (3 * tau) + 2) := by sorry
