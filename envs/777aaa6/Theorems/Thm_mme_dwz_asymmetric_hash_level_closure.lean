-- Prove2me | Theorems.Thm_mme_dwz_asymmetric_hash_level_closure
-- name    : mme_dwz_asymmetric_hash_level_closure
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-08T08:17:56.890313+00:00
-- url     : https://prove2.me/theorems/d6710be3-c913-4cd1-a8c5-747c54bc6277
-- title:
--   Retained affine-hash closure on the level set
-- statement:
--   Let `p` be a prime with `2` invertible mod `p`, and let a DWZ asymmetric hash state assign a weight to each coordinate together with the two scalars `w0` and `b0`. Given coordinate vectors `I`, `J`, `K` lying on the level set
--
--   $$ I_t + J_t + K_t = \text{levelSum} \quad \text{for every } t, $$
--
--   the three DWZ hashes satisfy the identity `X + Y = 2Z` for **every** state. Consequently, if the state sends `I` and `J` to a common value `s` under the `X` and `Y` hashes, it necessarily sends `K` to `s` under the `Z` hash.
--
--   This is the closure property underlying DWZ's asymmetric hashing: on the level set the `Z` condition carries no independent information, so three-way hash agreement is governed by two constraints rather than three. Nothing about the retained set or the extraction is assumed; the statement is an identity in the hash state.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, FOCS 2023, arXiv:2210.10173v5, Section 7.2 (printed p. 66) and Equation (34) (p. 71), https://arxiv.org/abs/2210.10173v5

import Definitions.Def_mme_dwz_asymmetric_affine_hash

open MME BigOperators

set_option autoImplicit false

theorem mme_dwz_asymmetric_hash_level_closure {p N : ℕ} [Fact p.Prime]
    (h2 : (2 : ZMod p) ≠ 0)
    (levelSum : ZMod p) (ω : DWZAsymmetricHashState p N)
    (I J K : Fin (N + 1) → ZMod p)
    (hlevel : ∀ t, I t + J t + K t = levelSum)
    (s : ZMod p)
    (hX : dwzAsymmetricHashX ω I = s)
    (hY : dwzAsymmetricHashY ω J = s) :
    dwzAsymmetricHashZ levelSum ω K = s := by sorry
