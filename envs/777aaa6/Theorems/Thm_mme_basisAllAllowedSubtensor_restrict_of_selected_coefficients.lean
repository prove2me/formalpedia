-- Prove2me | Theorems.Thm_mme_basisAllAllowedSubtensor_restrict_of_selected_coefficients
-- name    : mme_basisAllAllowedSubtensor_restrict_of_selected_coefficients
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T10:38:05.588189+00:00
-- url     : https://prove2.me/theorems/65280fcc-fe80-4f65-9aab-8c26da68504a
-- title:
--   Tensor restriction by selecting allowed basis coefficients
-- statement:
--   Let T and S be three-mode tensors over a field, with chosen mode bases b and c, and finite target basis index sets J_i. Let P_i specify the allowed source coordinates. Suppose maps e_i from target indices to source indices select allowed coordinates, and every coefficient of S equals the corresponding selected coefficient of T. Then S is a restriction of the simultaneous P-allowed basis subtensor of T. The coordinate maps e_i need not be injective.
-- source:
--   Coordinate linear maps and descent through the allowed-coordinate projection; extracted and generalized from the accepted boundary extraction proof.

import Theorems.Thm_mme_restrict_basisAllAllowedSubtensor_of_vanishes
import Mathlib.LinearAlgebra.PiTensorProduct.Basis

open MME MME.TensorObj Module PiTensorProduct
universe u
set_option autoImplicit false

theorem mme_basisAllAllowedSubtensor_restrict_of_selected_coefficients
    {K : Type u} [Field K] (T S : TensorObj K 3)
    {I : Fin 3 → Type u} {J : Fin 3 → Type u}
    [∀ i, Fintype (J i)]
    (b : ∀ i, Basis (I i) K (T.V i)) (c : ∀ i, Basis (J i) K (S.V i))
    (allowed : ∀ i, I i → Prop) (e : ∀ i, J i → I i)
    (he : ∀ i j, allowed i (e i j))
    (hc : ∀ w, (Basis.piTensorProduct b).repr T.t (fun i ↦ e i (w i)) =
      (Basis.piTensorProduct c).repr S.t w) :
    Restrict S (T.basisAllAllowedSubtensor b allowed) := by sorry
