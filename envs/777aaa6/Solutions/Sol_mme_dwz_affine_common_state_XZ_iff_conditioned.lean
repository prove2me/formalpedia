-- Prove2me | solution 1 for mme_dwz_affine_common_state_XZ_iff_conditioned
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-28T02:17:13.214203+00:00
-- url     : https://prove2.me/submissions/6ab6c837-b901-4252-b3e4-2f5754f34b79

import Theorems.Thm_mme_dwz_affine_retaining_state_w0_eq_conditioned

open MME BigOperators

set_option autoImplicit false
set_option warningAsError true

theorem solution
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
  dsimp only
  have hw0 := mme_dwz_affine_retaining_state_w0_eq_conditioned
    hpodd S I J K hsupport q hretains
  simp only [MME.dwzAsymmetricHashX, MME.dwzAsymmetricHashZ,
    MME.dwzAsymmetricHashStateOfAffine]
  rw [hw0]
  constructor
  · exact add_left_cancel
  · intro h
    exact congrArg (fun x ↦ q.1 (Fin.last (N + 1)) + x) h
