-- Prove2me | Theorems.Thm_mme_dwz_asymmetric_hash_AP_free_membership_iff_common_label
-- name    : mme_dwz_asymmetric_hash_AP_free_membership_iff_common_label
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T05:18:38.054797+00:00
-- url     : https://prove2.me/theorems/8208a826-354a-418d-8772-539305b8b537
-- title:
--   DWZ lower-half block survival is equivalent to one common hash label
-- statement:
--   Let $S\subseteq[0,p/2)$ be three-term-progression-free, and let a supported DWZ address be hashed by an odd-modulus affine state. The three separate conditions that its $X$, $Y$, and $Z$ hash values lie in the cast image of $S$ are equivalent to the existence of one common label in that image equal to all three hash values. This identifies the paper's block-zeroing rule with the common-label incidence predicate used in the first-moment and collision counts.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5 / FOCS 2023, Section 3.10.

import Definitions.Def_mme_dwz_asymmetric_affine_hash

set_option autoImplicit false
open MME

theorem mme_dwz_asymmetric_hash_AP_free_membership_iff_common_label
    {p N : ℕ} (hpodd : Odd p)
    (S : Finset ℕ) (hSrange : S ⊆ Finset.range (p / 2))
    (hSfree : ThreeAPFree (S : Set ℕ))
    (levelSum : ZMod p) (I J K : Fin (N + 1) → ZMod p)
    (hsupport : ∀ t, I t + J t + K t = levelSum)
    (q : (Fin (N + 2) → ZMod p) × ZMod p) :
    let castS : Finset (ZMod p) :=
      S.image (fun a : ℕ ↦ (a : ZMod p))
    let ω := dwzAsymmetricHashStateOfAffine q
    (dwzAsymmetricHashX ω I ∈ castS ∧
        dwzAsymmetricHashY ω J ∈ castS ∧
        dwzAsymmetricHashZ levelSum ω K ∈ castS) ↔
      dwzAsymmetricAffineRetains levelSum castS I J K q := by
  sorry
