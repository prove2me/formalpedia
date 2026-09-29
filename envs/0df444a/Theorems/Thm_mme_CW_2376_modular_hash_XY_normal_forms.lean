-- Prove2me | Theorems.Thm_mme_CW_2376_modular_hash_XY_normal_forms
-- name    : mme_CW_2376_modular_hash_XY_normal_forms
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T21:33:59.472985+00:00
-- url     : https://prove2.me/theorems/9b5c79fb-b63b-4b8b-8e71-9ef337521854
-- title:
--   The odd-modulus CW X and Y hashes have linear-affine normal form
-- statement:
--   For an odd modulus, the ordinary first-mode CW hash is the linear form whose coefficients are the five-grades of the word. The second-mode hash is the analogous linear form plus its affine offset.
--
--   These normal forms connect the source's doubled hash definitions to exact finite-field fiber counting: a positive grade supplies a nonzero coefficient for the first hash, and the second hash determines the affine offset uniquely.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), affine outer hashes on journal p. 268; https://doi.org/10.1016/S0747-7171(08)80013-2

import Definitions.Def_mme_CW_2376_modular_hash

open MME BigOperators

theorem mme_CW_2376_modular_hash_XY_normal_forms
    {p N : ℕ} (hpodd : Odd p)
    (b0 : ZMod p) (w : Fin N → ZMod p)
    (x y : Fin N → Fin 5) :
    cw2376XHashMod w x =
        ∑ j, ((x j).val : ZMod p) * w j ∧
      cw2376YHashMod b0 w y =
        b0 + ∑ j, ((y j).val : ZMod p) * w j := by
  sorry
