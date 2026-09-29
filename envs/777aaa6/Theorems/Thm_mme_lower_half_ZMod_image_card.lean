-- Prove2me | Theorems.Thm_mme_lower_half_ZMod_image_card
-- name    : mme_lower_half_ZMod_image_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T21:36:06.612848+00:00
-- url     : https://prove2.me/theorems/f121aab6-e6a3-4798-bd8d-0c38936d248b
-- title:
--   Lower-half integer labels cast injectively into a residue ring
-- statement:
--   If a finite set of natural-number labels lies below half of a modulus $p$, then casting those labels into the residue ring modulo $p$ is injective on the set. Consequently its residue image has exactly the same cardinality.
--
--   This elementary bridge lets lower-half Salem--Spencer sets be inserted into exact modular hash fiber counts without losing labels to residue collisions.
-- source:
--   Elementary modular arithmetic; used with lower-half progression-free label sets in the affine hashing of D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), pp. 259--261 and 267--269; https://doi.org/10.1016/S0747-7171(08)80013-2

import Mathlib.Data.ZMod.Basic

theorem mme_lower_half_ZMod_image_card
    (p : ℕ) (S : Finset ℕ)
    (hSrange : S ⊆ Finset.range (p / 2)) :
    (S.image (fun s : ℕ => (s : ZMod p))).card = S.card := by
  sorry
