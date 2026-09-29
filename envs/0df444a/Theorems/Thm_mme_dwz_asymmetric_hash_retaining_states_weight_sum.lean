-- Prove2me | Theorems.Thm_mme_dwz_asymmetric_hash_retaining_states_weight_sum
-- name    : mme_dwz_asymmetric_hash_retaining_states_weight_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T20:59:06.025498+00:00
-- url     : https://prove2.me/theorems/92f0cead-c785-4e7c-8d08-c2bfe13d5845
-- title:
--   Retaining affine states repeat every weight mass exactly |S| times
-- statement:
--   For a supported component triple, project each retaining affine state to its first N+1 coordinates. Every weight word has exactly |S| retaining affine states above it. Consequently, summing any natural-valued mass that depends only on this weight over all retaining states equals |S| times its sum over all weight words.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, asymmetric hash-state construction and Claim 6.8 averaging; https://arxiv.org/abs/2210.10173

import Theorems.Thm_mme_dwz_asymmetric_hash_retaining_states_weight_filter_card

open BigOperators

set_option autoImplicit false

theorem mme_dwz_asymmetric_hash_retaining_states_weight_sum
    {p N : ℕ} [Fact p.Prime] (hpodd : Odd p)
    (levelSum : ZMod p) (S : Finset (ZMod p))
    (I J K : Fin (N + 1) → ZMod p)
    (hsupport : ∀ t, I t + J t + K t = levelSum)
    (mass : (Fin (N + 1) → ZMod p) → ℕ) :
    ∑ q ∈ MME.dwzAsymmetricAffineStatesRetaining
        levelSum S I J K,
        mass (fun t ↦ q.1 t.castSucc) =
      S.card * ∑ w : Fin (N + 1) → ZMod p, mass w := by
  sorry
