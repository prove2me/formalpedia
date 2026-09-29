-- Prove2me | Theorems.Thm_mme_dwz_lemma3_11_fixed_z_collision_fiber
-- name    : mme_dwz_lemma3_11_fixed_z_collision_fiber
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T11:00:40.816787+00:00
-- url     : https://prove2.me/theorems/f6695d7c-ef14-4a3a-b0ab-13ab6e03716c
-- title:
--   DWZ Lemma 3.11: exact fixed-Z conditional collision fiber
-- statement:
--   Let $p$ be an odd prime. Fix a level sum $L$, an affine constant $b_0$, a Z-address $K$, and distinct X-addresses $I,I'$, all modulo $p$. Use the DWZ hashes
--
--   $$h_X(A)=b_0+\sum_t A_tw_t,\qquad h_Z(K)=b_0+2^{-1}\left(w_0+\sum_t(L-K_t)w_t\right).$$
--
--   The conditioning equation $h_X(I)=h_Z(K)$ determines $w_0$ uniquely as $2\sum_t I_tw_t-\sum_t(L-K_t)w_t$. In this exactly parametrized conditional space $\Omega$ of remaining weight vectors, the collision fiber has density exactly $1/p$:
--
--   $$p\,\bigl|\{w\in\Omega:h_X(I')=h_Z(K)\}\bigr|=|\Omega|.$$
--
--   This is the concrete, division-free Lemma 3.11 premise needed by the finite Claim 6.8 union bound.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5 / FOCS 2023, Section 3.10, Lemma 3.11 (printed pp. 25-26 / PDF pp. 26-27).

import Mathlib
import Theorems.Thm_mme_ZMod_prime_linear_hash_fiber_card
open BigOperators
set_option autoImplicit false

theorem mme_dwz_lemma3_11_fixed_z_collision_fiber
    {p n : ℕ} [Fact p.Prime] (hpodd : Odd p)
    (levelSum b0 : ZMod p)
    (I I' K : Fin (n + 1) → ZMod p) (hII' : I ≠ I') :
    let hX : (Fin (n + 1) → ZMod p) →
        (Fin (n + 1) → ZMod p) → ZMod p :=
      fun w A => b0 + ∑ t, A t * w t
    let hZ : ZMod p → (Fin (n + 1) → ZMod p) →
        (Fin (n + 1) → ZMod p) → ZMod p :=
      fun w0 w C =>
        b0 + (2 : ZMod p)⁻¹ *
          (w0 + ∑ t, (levelSum - C t) * w t)
    let conditionedW0 : (Fin (n + 1) → ZMod p) → ZMod p :=
      fun w =>
        2 * (∑ t, I t * w t) -
          ∑ t, (levelSum - K t) * w t
    (∀ w w0, hX w I = hZ w0 w K ↔ w0 = conditionedW0 w) ∧
      p * ((Finset.univ.filter
        (fun w : Fin (n + 1) → ZMod p =>
          hX w I' = hZ (conditionedW0 w) w K)).card) =
        Fintype.card (Fin (n + 1) → ZMod p) := by sorry
