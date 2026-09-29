-- Prove2me | Theorems.Thm_mme_dwz_lemma3_11_bounded_address_collision_fiber
-- name    : mme_dwz_lemma3_11_bounded_address_collision_fiber
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T11:12:01.091324+00:00
-- url     : https://prove2.me/theorems/5051603d-d691-42c9-ad17-e74fafac442c
-- title:
--   DWZ Lemma 3.11 for bounded natural block addresses
-- statement:
--   Let $p$ be an odd prime and let $0\le L<p$. Take distinct X-address words $I,I'$ and a Z-address word $K$, each of positive length and with entries in $\{0,\ldots,L\}$. For the DWZ affine hashes
--
--   $$h_X(A)=b_0+\sum_t A_tw_t,\qquad h_Z(C)=b_0+2^{-1}\left(w_0+\sum_t(L-C_t)w_t\right)\pmod p,$$
--
--   the conditioning equation $h_X(I)=h_Z(K)$ uniquely determines $w_0$. Among the remaining weight vectors, the competing collision has exact density $1/p$:
--
--   $$p\,|\{w:h_X(I')=h_Z(K)\}|=|\Omega|.$$
--
--   The hypothesis $L<p$ proves that distinct bounded integer addresses remain distinct modulo $p$, closing the concrete address-casting interface needed when Lemma 3.11 is used in Claim 6.8.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5 / FOCS 2023, Section 3.10, Lemma 3.11 (printed pp. 25-26 / PDF pp. 26-27).

import Mathlib
import Theorems.Thm_mme_dwz_lemma3_11_fixed_z_collision_fiber

open BigOperators
set_option autoImplicit false

theorem mme_dwz_lemma3_11_bounded_address_collision_fiber
    {p n levelSum : ℕ} [Fact p.Prime]
    (hpodd : Odd p) (hlevel : levelSum < p) (b0 : ZMod p)
    (I I' K : Fin (n + 1) → Fin (levelSum + 1)) (hII' : I ≠ I') :
    let hX : (Fin (n + 1) → ZMod p) →
        (Fin (n + 1) → Fin (levelSum + 1)) → ZMod p :=
      fun w A => b0 + ∑ t, ((A t).val : ZMod p) * w t
    let hZ : ZMod p → (Fin (n + 1) → ZMod p) →
        (Fin (n + 1) → Fin (levelSum + 1)) → ZMod p :=
      fun w0 w C =>
        b0 + (2 : ZMod p)⁻¹ *
          (w0 + ∑ t,
            ((levelSum : ZMod p) - (C t).val) * w t)
    let conditionedW0 : (Fin (n + 1) → ZMod p) → ZMod p :=
      fun w =>
        2 * (∑ t, ((I t).val : ZMod p) * w t) -
          ∑ t, ((levelSum : ZMod p) - (K t).val) * w t
    (∀ w w0, hX w I = hZ w0 w K ↔ w0 = conditionedW0 w) ∧
      p * ((Finset.univ.filter
        (fun w : Fin (n + 1) → ZMod p =>
          hX w I' = hZ (conditionedW0 w) w K)).card) =
        Fintype.card (Fin (n + 1) → ZMod p) := by sorry
