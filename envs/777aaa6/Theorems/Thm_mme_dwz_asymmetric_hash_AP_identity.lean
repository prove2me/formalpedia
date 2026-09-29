-- Prove2me | Theorems.Thm_mme_dwz_asymmetric_hash_AP_identity
-- name    : mme_dwz_asymmetric_hash_AP_identity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T04:20:38.227433+00:00
-- url     : https://prove2.me/theorems/94876b1f-1989-464a-afc8-75230d28e92f
-- title:
--   DWZ affine hashes satisfy the three-term progression identity
-- statement:
--   For an odd modulus $p$, let $(I,J,K)$ be a supported address whose three coordinate grades sum to the common level at every position. The three affine hash values from DWZ Section 3.10 satisfy
--
--   $$h_X(I)+h_Y(J)=2h_Z(K) \pmod p.$$
--
--   This is the exact arithmetic-progression identity that lets a lower-half three-term-progression-free set force all three retained hash labels to coincide.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5 / FOCS 2023, Section 3.10, displayed hash formulas and following identity on printed p. 25.

import Definitions.Def_mme_dwz_asymmetric_affine_hash

open BigOperators
set_option autoImplicit false

open MME

theorem mme_dwz_asymmetric_hash_AP_identity
    {p N : ℕ} (hpodd : Odd p) (levelSum : ZMod p)
    (ω : DWZAsymmetricHashState p N)
    (I J K : Fin (N + 1) → ZMod p)
    (hsupport : ∀ t, I t + J t + K t = levelSum) :
    dwzAsymmetricHashX ω I + dwzAsymmetricHashY ω J =
      2 * dwzAsymmetricHashZ levelSum ω K := by
  sorry
