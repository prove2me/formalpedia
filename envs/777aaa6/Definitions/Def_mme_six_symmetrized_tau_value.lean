-- Prove2me | Definitions.Def_mme_six_symmetrized_tau_value
-- name    : mme_six_symmetrized_tau_value
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-08-25T09:37:15.847534+00:00
-- url     : https://prove2.me/theorems/4a2d47f3-8640-412f-8b5d-cd101d131983
-- title:
--   Definition 3.3: six-symmetrized tau-value witnesses
-- statement:
--   Define DWZ's full symmetrization as cyclic symmetrization tensored
--   with the first-two-modes swap of that cyclic symmetrization. Define
--   `HasSixSymmetricTauValueAtLeast T tau V` to mean that this six-factor product
--   has direct tau-value base at least `V^6`. This is the witness-level form of DWZ
--   Definition 3.3 and keeps the sixth-root normalization explicit.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, FOCS 2023, arXiv:2210.10173, Definition 3.3 (printed p. 18).

import Definitions.Def_mme_CW_coupled_value
import Definitions.Def_mme_permutation

/-!
# Six-symmetrized tau-value

This is the full symmetrization in Duan--Wu--Zhou, Definition 3.3:
`sym6(T) = sym3(T) ⊗ sym3(T)^swap`, where `swap` exchanges the first
two tensor modes.
-/

universe u

namespace MME

/-- The transposition of the first two modes of an order-three tensor. -/
def swapFirstTwoPerm : Equiv.Perm (Fin 3) where
  toFun
    | ⟨0, _⟩ => ⟨1, by norm_num⟩
    | ⟨1, _⟩ => ⟨0, by norm_num⟩
    | ⟨2, _⟩ => ⟨2, by norm_num⟩
    | ⟨n + 3, h⟩ => absurd h (by omega)
  invFun
    | ⟨0, _⟩ => ⟨1, by norm_num⟩
    | ⟨1, _⟩ => ⟨0, by norm_num⟩
    | ⟨2, _⟩ => ⟨2, by norm_num⟩
    | ⟨n + 3, h⟩ => absurd h (by omega)
  left_inv := by decide
  right_inv := by decide

/-- DWZ Definition 3.3's full symmetrization
`sym6(T) = sym3(T) ⊗ sym3(T)^swap`. -/
noncomputable def sixSymmetrization
    {K : Type u} [Field K] (T : TensorObj K 3) : TensorObj K 3 :=
  TensorObj.kron (cyclicSymmetrization T)
    (TensorObj.permObj swapFirstTwoPerm (cyclicSymmetrization T))

/-- `T` has six-symmetrized tau-value at least `V` when `sym6(T)` has
direct tau-value at least `V^6`, matching the sixth-root normalization in
DWZ Definition 3.3. -/
def HasSixSymmetricTauValueAtLeast
    {K : Type u} [Field K] (T : TensorObj K 3) (tau V : ℝ) : Prop :=
  HasTauValueAtLeast (sixSymmetrization T) tau (V ^ (6 : ℕ))

end MME


