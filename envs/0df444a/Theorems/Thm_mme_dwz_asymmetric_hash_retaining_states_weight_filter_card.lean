-- Prove2me | Theorems.Thm_mme_dwz_asymmetric_hash_retaining_states_weight_filter_card
-- name    : mme_dwz_asymmetric_hash_retaining_states_weight_filter_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T20:34:39.816532+00:00
-- url     : https://prove2.me/theorems/a4e7c57c-b912-4955-91fa-b921c798644d
-- title:
--   Every admissible DWZ weight has exactly one retaining state per common label
-- statement:
--   Fix a supported triple of address words and a finite family W of admissible hash-weight words. Among the DWZ affine states retaining that triple, the number whose weight belongs to W is exactly |S||W|. Equivalently, each weight has one retaining affine state for every common label in S.
-- source:
--   Duan--Wu--Zhou asymmetric affine hashing; refined singleton incidence count needed to lift Claim 6.8 from weights to common affine states.

import Theorems.Thm_mme_dwz_asymmetric_affine_retains_iff_weight_label

open BigOperators
open MME

set_option autoImplicit false

theorem mme_dwz_asymmetric_hash_retaining_states_weight_filter_card
    {p N : ℕ} [Fact p.Prime] (hpodd : Odd p)
    (levelSum : ZMod p) (S : Finset (ZMod p))
    (I J K : Fin (N + 1) → ZMod p)
    (hsupport : ∀ t, I t + J t + K t = levelSum)
    (W : Finset (Fin (N + 1) → ZMod p)) :
    ((MME.dwzAsymmetricAffineStatesRetaining levelSum S I J K).filter
      (fun q ↦ (fun t ↦ q.1 t.castSucc) ∈ W)).card =
        S.card * W.card := by
  sorry
