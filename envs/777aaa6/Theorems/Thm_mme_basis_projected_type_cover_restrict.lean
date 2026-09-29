-- Prove2me | Theorems.Thm_mme_basis_projected_type_cover_restrict
-- name    : mme_basis_projected_type_cover_restrict
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-13T14:40:16.307062+00:00
-- url     : https://prove2.me/theorems/e1a4129f-8b4f-4eae-b304-95805988e4e7
-- title:
--   Reconstruct a projected tensor from its exact type pieces
-- statement:
--   Let T have finite mode bases and let P be an allowed predicate in each mode. Suppose Q_j is contained in P in every mode, and every nonzero retained coefficient belongs to exactly one complete three-mode Q_j type. Then the actual P-projected tensor restricts from the direct sum of the actual Q_j-projected tensors. This direction deliberately allows the target pieces to share variables after the map. In the recursion, it reconstructs a tolerance band from exact profile cases and charges one independent input per case.
-- source:
--   Finite algebraic ingredients for Alman et al., More Asymmetry Yields Faster Matrix Multiplication, https://arxiv.org/html/2404.16349v2#S6 , Proposition 6.3, Theorem 6.4, and Sections 6.5–6.6. These statements retain explicit finite hole budgets and type-copy overheads; they do not assert the entropy asymptotics or numerical certificate.

import Definitions.Def_mme_complete_split_profile_projection
import Definitions.Def_mme_TypeGrading_kron
import Definitions.Def_mme_tensor_rank
import Mathlib.LinearAlgebra.PiTensorProduct.Basis

open MME Module PiTensorProduct BigOperators
universe u
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

theorem mme_basis_projected_type_cover_restrict {K : Type u} [Field K] (T : TensorObj K 3) {k : ℕ}
    {I : Fin 3 → Type u} [∀ i, Fintype (I i)]
    (b : ∀ i, Basis (I i) K (T.V i))
    (parent : ∀ i, I i → Prop) (keep : Fin k → ∀ i, I i → Prop)
    (hsub : ∀ j i x, keep j i x → parent i x)
    (hcover : ∀ (x : ∀ i, I i), (Basis.piTensorProduct b).repr T.t x ≠ 0 →
      (∀ i, parent i (x i)) → ∃! j, ∀ i, keep j i (x i)) :
    TensorObj.Restrict (T.basisAllAllowedSubtensor b parent)
      (TensorObj.bigAdd (fun j ↦ T.basisAllAllowedSubtensor b (keep j))) := by sorry
