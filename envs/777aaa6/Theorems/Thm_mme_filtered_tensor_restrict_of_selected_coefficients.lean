-- Prove2me | Theorems.Thm_mme_filtered_tensor_restrict_of_selected_coefficients
-- name    : mme_filtered_tensor_restrict_of_selected_coefficients
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T10:44:54.587779+00:00
-- url     : https://prove2.me/theorems/e07046bd-8586-4244-9116-e9f8977d9ce9
-- title:
--   Filtered tensor restriction by selected coefficients
-- statement:
--   Let $T$ and $S$ be three-mode tensors over a field $K$, with mode bases indexed by $I_i$ and finite sets $J_i$, respectively. Let $P_i\subseteq I_i$ and $Q_i\subseteq J_i$ be the allowed coordinates. Suppose maps $e_i:J_i\to I_i$ send every $Q_i$-allowed index to a $P_i$-allowed index, and the tensor coefficients satisfy
--   $$S_{j_0,j_1,j_2}=T_{e_0(j_0),e_1(j_1),e_2(j_2)}.$$
--   Then the simultaneous coordinate projections satisfy
--   $$S[Q]\preceq T[P].$$
--   No injectivity of the coordinate maps is required. This supplies actual modewise restriction maps between filtered tensors, including empty allowed sets.
-- source:
--   Canonical-to-intact tensor transport: finite coordinate maps and coefficient preservation.

import Theorems.Thm_mme_restrict_basisAllAllowedSubtensor_of_vanishes
import Mathlib.LinearAlgebra.PiTensorProduct.Basis

open MME MME.TensorObj Module PiTensorProduct
open scoped Classical
universe u
set_option autoImplicit false

theorem mme_filtered_tensor_restrict_of_selected_coefficients
    {K : Type u} [Field K] (T S : TensorObj K 3)
    {I J : Fin 3 → Type u} [∀ i, Fintype (J i)]
    (b : ∀ i, Basis (I i) K (T.V i)) (c : ∀ i, Basis (J i) K (S.V i))
    (P : ∀ i, I i → Prop) (Q : ∀ i, J i → Prop) (e : ∀ i, J i → I i)
    (he : ∀ i j, Q i j → P i (e i j))
    (hc : ∀ w, (Basis.piTensorProduct b).repr T.t (fun i ↦ e i (w i)) =
      (Basis.piTensorProduct c).repr S.t w) :
    Restrict (S.basisAllAllowedSubtensor c Q) (T.basisAllAllowedSubtensor b P) := by sorry
