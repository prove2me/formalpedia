-- Prove2me | Theorems.Thm_mme_dwz_asymmetric_affine_retains_iff_of_level
-- name    : mme_dwz_asymmetric_affine_retains_iff_of_level
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-08T08:17:52.214244+00:00
-- url     : https://prove2.me/theorems/5126b4f6-4bf7-4030-b7f5-b7853ca3621d
-- title:
--   Affine retention collapses to two hash conditions on the level set
-- statement:
--   For coordinate vectors `I`, `J`, `K` on the level set `I_t + J_t + K_t = levelSum`, an affine state retains the triple exactly when its `X` and `Y` hashes agree on a common element of the retained set `S` — the `Z` condition is automatic.
--
--   This is the retention-level form of the level-set closure identity, stated for the predicate the extraction argument actually consumes. It replaces a three-condition membership test by a two-condition one, which is what makes the asymmetric-hashing count tractable; it is not itself an extraction or a size bound.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, FOCS 2023, arXiv:2210.10173v5, Section 7.2 (printed p. 66) and Equation (34) (p. 71), https://arxiv.org/abs/2210.10173v5

import Definitions.Def_mme_dwz_asymmetric_affine_hash

open MME BigOperators

set_option autoImplicit false

theorem mme_dwz_asymmetric_affine_retains_iff_of_level {p N : ℕ} [Fact p.Prime]
    (h2 : (2 : ZMod p) ≠ 0)
    (levelSum : ZMod p) (S : Finset (ZMod p))
    (I J K : Fin (N + 1) → ZMod p)
    (hlevel : ∀ t, I t + J t + K t = levelSum)
    (q : (Fin (N + 2) → ZMod p) × ZMod p) :
    dwzAsymmetricAffineRetains levelSum S I J K q ↔
      ∃ s ∈ S,
        dwzAsymmetricHashX (dwzAsymmetricHashStateOfAffine q) I = s ∧
        dwzAsymmetricHashY (dwzAsymmetricHashStateOfAffine q) J = s := by sorry
