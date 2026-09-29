-- Prove2me | Theorems.Thm_mme_stothers_phi233_lower_half_cast_label_package
-- name    : mme_stothers_phi233_lower_half_cast_label_package
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-03T00:18:40.915682+00:00
-- url     : https://prove2.me/theorems/84a45c65-220c-4b0d-9932-4a76db14d615
-- title:
--   Lower-half progression-free labels embed faithfully in ZMod
-- statement:
--   A natural-number three-term-progression-free set contained below half the modulus embeds in ZMod p without losing cardinality, and its image has no nonconstant three-term arithmetic progression in the field. This packages the exact label-set interface needed by the Phi233 affine-hash pruning construction.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Lemma 3.3 and the progression-free hashing construction; formal packaging of the standard lower-half embedding into a prime cyclic field.

import Theorems.Thm_mme_lower_half_ZMod_image_card
import Theorems.Thm_mme_dwz_threeAP_free_cast_labels_collapse

set_option autoImplicit false

theorem mme_stothers_phi233_lower_half_cast_label_package
    (p : ℕ) (S : Finset ℕ)
    (hSrange : S ⊆ Finset.range (p / 2))
    (hSfree : ThreeAPFree (S : Set ℕ)) :
    let castS := S.image (fun s : ℕ => (s : ZMod p))
    castS.card = S.card ∧
      ∀ a ∈ castS, ∀ b ∈ castS, ∀ c ∈ castS,
        a + b = 2 * c → a = c ∧ c = b := by
  sorry
