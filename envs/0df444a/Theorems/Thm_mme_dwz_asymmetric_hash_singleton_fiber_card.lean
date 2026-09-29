-- Prove2me | Theorems.Thm_mme_dwz_asymmetric_hash_singleton_fiber_card
-- name    : mme_dwz_asymmetric_hash_singleton_fiber_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T04:27:20.66142+00:00
-- url     : https://prove2.me/theorems/f2988b77-4a7d-4f94-bfe5-5f9c6fb64640
-- title:
--   Exact one-address incidence for the DWZ affine hash
-- statement:
--   Fix a supported DWZ address $(I,J,K)$ of length $N+1$ over an odd prime field and a finite common-label set $S$. Among all literal affine states $(w,w_0,b_0)$, exactly
--
--   $$|S|p^{N+1}$$
--
--   states map all three blocks to one common label in $S$. This is the exact $|B|M^{-2}$ one-triple incidence underlying the Section 3.10 first moment.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5 / FOCS 2023, Section 3.10, first-moment calculation on printed pp. 25–26.

import Definitions.Def_mme_dwz_asymmetric_affine_hash
import Theorems.Thm_mme_dwz_asymmetric_hash_AP_identity
import Theorems.Thm_mme_ZMod_prime_linear_hash_affine_graph_finset_card

open BigOperators
set_option autoImplicit false
open MME

theorem mme_dwz_asymmetric_hash_singleton_fiber_card
    {p N : ℕ} [Fact p.Prime] (hpodd : Odd p)
    (levelSum : ZMod p) (S : Finset (ZMod p))
    (I J K : Fin (N + 1) → ZMod p)
    (hsupport : ∀ t, I t + J t + K t = levelSum) :
    (dwzAsymmetricAffineStatesRetaining
      levelSum S I J K).card = S.card * p ^ (N + 1) := by
  sorry
