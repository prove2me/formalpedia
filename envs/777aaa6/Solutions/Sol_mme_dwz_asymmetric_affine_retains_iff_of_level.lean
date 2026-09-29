-- Prove2me | solution 1 for mme_dwz_asymmetric_affine_retains_iff_of_level
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-08T08:19:23.643645+00:00
-- url     : https://prove2.me/submissions/6c9a9bab-88eb-41f5-a61f-7d44c5909de9

import Theorems.Thm_mme_dwz_asymmetric_hash_level_closure
open MME BigOperators
set_option autoImplicit false

theorem solution {p N : ℕ} [Fact p.Prime]
    (h2 : (2 : ZMod p) ≠ 0)
    (levelSum : ZMod p) (S : Finset (ZMod p))
    (I J K : Fin (N + 1) → ZMod p)
    (hlevel : ∀ t, I t + J t + K t = levelSum)
    (q : (Fin (N + 2) → ZMod p) × ZMod p) :
    dwzAsymmetricAffineRetains levelSum S I J K q ↔
      ∃ s ∈ S,
        dwzAsymmetricHashX (dwzAsymmetricHashStateOfAffine q) I = s ∧
        dwzAsymmetricHashY (dwzAsymmetricHashStateOfAffine q) J = s := by
  constructor
  · rintro ⟨s, hs, hX, hY, -⟩
    exact ⟨s, hs, hX, hY⟩
  · rintro ⟨s, hs, hX, hY⟩
    exact ⟨s, hs, hX, hY,
      mme_dwz_asymmetric_hash_level_closure h2 levelSum _ I J K hlevel s hX hY⟩
