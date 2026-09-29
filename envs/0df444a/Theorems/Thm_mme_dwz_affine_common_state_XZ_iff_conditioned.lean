-- Prove2me | Theorems.Thm_mme_dwz_affine_common_state_XZ_iff_conditioned
-- name    : mme_dwz_affine_common_state_XZ_iff_conditioned
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-28T02:17:00.430217+00:00
-- url     : https://prove2.me/theorems/fe7d3b4c-da55-48e4-8f0e-f967a81f01f9
-- title:
--   Common-state X–Z hash equality is the conditioned Claim-6.8 equation
-- statement:
--   Let an affine state $q$ retain a supported triple $(I,J,K)$ of words over $\mathbb Z/p\mathbb Z$, where $p$ is odd and $I_t+J_t+K_t=4$ at every coordinate. Write $\omega$ for the state weight word and
--
--   $$
--   c=2\sum_t I_t\omega_t-\sum_t(4-K_t)\omega_t.
--   $$
--
--   Then, for every candidate word $X$, equality of its affine $X$ hash with the retained $Z$ hash is equivalent to the conditioned weighted-sum equation
--
--   $$
--   h_X(X)=h_Z(K)\quad\Longleftrightarrow\quad
--   \sum_tX_t\omega_t=2^{-1}\left(c+\sum_t(4-K_t)\omega_t\right).
--   $$
--
--   This identifies the common affine state used by the global first hash with the conditioned second-hash relation used in the Claim-6.8 nonhole construction.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, the conditioned asymmetric-hash construction in Claim 6.8 (printed pp. 56–57; PDF pp. 57–58); https://arxiv.org/abs/2210.10173

import Theorems.Thm_mme_dwz_affine_retaining_state_w0_eq_conditioned

open MME BigOperators

set_option autoImplicit false

theorem mme_dwz_affine_common_state_XZ_iff_conditioned
    {p N : ℕ} [Fact p.Prime] (hpodd : Odd p)
    (S : Finset (ZMod p))
    (I J K X : Fin (N + 1) → ZMod p)
    (hsupport : ∀ t, I t + J t + K t = (4 : ZMod p))
    (q : (Fin (N + 2) → ZMod p) × ZMod p)
    (hretains : MME.dwzAsymmetricAffineRetains
      (4 : ZMod p) S I J K q) :
    let weight : Fin (N + 1) → ZMod p := fun t ↦ q.1 t.castSucc
    let conditionedW0 : ZMod p :=
      2 * (∑ t, I t * weight t) -
        ∑ t, ((4 : ZMod p) - K t) * weight t
    MME.dwzAsymmetricHashX
          (MME.dwzAsymmetricHashStateOfAffine q) X =
        MME.dwzAsymmetricHashZ (4 : ZMod p)
          (MME.dwzAsymmetricHashStateOfAffine q) K ↔
      (∑ t, X t * weight t) =
        (2 : ZMod p)⁻¹ *
          (conditionedW0 +
            ∑ t, ((4 : ZMod p) - K t) * weight t) := by
  sorry
