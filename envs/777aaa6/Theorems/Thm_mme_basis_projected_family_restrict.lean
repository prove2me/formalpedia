-- Prove2me | Theorems.Thm_mme_basis_projected_family_restrict
-- name    : mme_basis_projected_family_restrict
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-13T14:23:01.007256+00:00
-- url     : https://prove2.me/theorems/d557103e-4827-4e36-864d-3a357e770320
-- title:
--   Direct-sum extraction inside an existing parent projection
-- statement:
--   Let T have finite mode bases. For each j, let Q_j be a coordinate predicate contained in a parent predicate P in each mode. Suppose every nonzero coefficient retained by a mixed choice of Q_j owners has the same owner in all three modes. Then the direct sum of the actual simultaneous Q_j projections restricts from the actual P projection of T. This is a mode-wise linear restriction and preserves entire owner tensors, including shared internal variables. The parent projection is part of the source; it is not discarded.
-- source:
--   Finite projected-source algebra for Alman et al., More Asymmetry Yields Faster Matrix Multiplication, arXiv:2404.16349v2, Sections 6.2–6.5, especially Proposition 6.3. https://arxiv.org/html/2404.16349v2#S6 . The arbitrary parent predicate and explicit finite hypotheses are an adapter for the recursive source; this is not the full asymptotic proposition.

import Theorems.Thm_mme_tensor_family_direct_sum_restrict_of_mixed_maps
import Definitions.Def_mme_complete_split_profile_projection
import Definitions.Def_mme_TypeGrading_kron
import Mathlib.LinearAlgebra.PiTensorProduct.Basis

open MME Module PiTensorProduct BigOperators
universe u
set_option autoImplicit false
set_option maxHeartbeats 800000

theorem mme_basis_projected_family_restrict
    {K : Type u} [Field K] (T : TensorObj K 3) {k : ℕ}
    {I : Fin 3 → Type u} [∀ i, Fintype (I i)]
    (b : ∀ i, Basis (I i) K (T.V i))
    (parent : ∀ i, I i → Prop) (keep : Fin k → ∀ i, I i → Prop)
    (hsub : ∀ j i x, keep j i x → parent i x)
    (hunique : ∀ (x : ∀ i, I i) (js : Fin 3 → Fin k),
      (Basis.piTensorProduct b).repr T.t x ≠ 0 →
      (∀ i, keep (js i) i (x i)) → ∃ j, js = fun _ ↦ j) :
    TensorObj.Restrict
      (TensorObj.bigAdd (fun j ↦ T.basisAllAllowedSubtensor b (keep j)))
      (T.basisAllAllowedSubtensor b parent) := by sorry
