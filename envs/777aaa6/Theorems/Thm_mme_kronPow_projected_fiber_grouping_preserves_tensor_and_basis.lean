-- Prove2me | Theorems.Thm_mme_kronPow_projected_fiber_grouping_preserves_tensor_and_basis
-- name    : mme_kronPow_projected_fiber_grouping_preserves_tensor_and_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-17T08:14:51.048087+00:00
-- url     : https://prove2.me/theorems/df046091-059e-440f-aa1f-c6aa61ea0e63
-- title:
--   Exact fiber regrouping of coordinate-projected tensor powers
-- statement:
--   Let $T$ be a trilinear tensor with chosen mode bases. Let $n_c$ be finitely many nonnegative multiplicities and fix a bijection from the $N$ positions to the disjoint union of the sets $[n_c]$. In each component and mode, prescribe an arbitrary predicate on the component's basis word. Keep an original basis word exactly when all its grouped component words satisfy these predicates.
--
--   Write $U=\bigotimes_c T^{\otimes n_c}$, and use its product word basis. There are actual linear equivalences between the projected mode spaces such that
--   $$
--   (\bigotimes_i F_i)(T^{\otimes N})[P]=U[Q],
--   $$
--   where $P$ is the original-word predicate and $Q$ is the corresponding grouped-word predicate. These equivalences also satisfy the exact projected-basis formula
--   $$
--   F_i\pi_{P,i}(b_i(w))
--    =\pi_{Q,i}\bigl(c_i((w(e^{-1}(c,r)))_{c,r})\bigr).
--   $$
--
--   Thus coarse restrictions, exact profiles, or further componentwise masks can be transported through position regrouping without losing basis labels. Zero multiplicities are allowed, with the tensor-unit convention. The target here is a single coordinate projection of the product of raw powers; identifying it with a product of individually projected constituent tensors is a separate factorization step.
-- source:
--   Derived basis-aware grouping interface for Duan–Wu–Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section 5.1, Definitions 5.2–5.4 and Section 6.1. https://arxiv.org/html/2210.10173v5#S5.SS1 . This general algebraic regrouping lemma is not separately stated in the paper.

import Theorems.Thm_mme_kronPow_fiber_grouping_preserves_tensor_and_basis
import Theorems.Thm_mme_basisAllAllowedSubtensor_basis_equiv_transport
open MME Module PiTensorProduct
universe u
set_option autoImplicit false

theorem mme_kronPow_projected_fiber_grouping_preserves_tensor_and_basis
    {K : Type u} [Field K] {N k : ℕ} (T : TensorObj K 3)
    {I : Fin 3 → Type u} (b : ∀ i, Basis (I i) K (T.V i))
    (count : Fin k → ℕ) (positions : Fin N ≃ (Σ c, Fin (count c)))
    (allowed : ∀ c i, (Fin (count c) → I i) → Prop) :
    let U := TensorObj.kronFin k (fun c ↦ T.kronPow (count c))
    let B := fun i ↦ TensorObj.kronPowModeWordBasis T i (b i) N
    let C := fun i ↦ TensorObj.kronFinModePiBasis k
      (fun c ↦ T.kronPow (count c)) i
      (fun c ↦ TensorObj.kronPowModeWordBasis T i (b i) (count c))
    let P := fun i (w : Fin N → I i) ↦
      ∀ c, allowed c i (fun r ↦ w (positions.symm ⟨c, r⟩))
    let Q := fun i (w : ∀ c, Fin (count c) → I i) ↦ ∀ c, allowed c i (w c)
    ∃ f : ∀ i, ((T.kronPow N).basisAllAllowedGrading B P).classOf i 0 ≃ₗ[K]
        (U.basisAllAllowedGrading C Q).classOf i 0,
      PiTensorProduct.map (fun i ↦ (f i).toLinearMap)
        ((T.kronPow N).basisAllAllowedSubtensor B P).t =
          (U.basisAllAllowedSubtensor C Q).t ∧
      ∀ i w, f i (((T.kronPow N).basisAllAllowedGrading B P).blockProj i 0
        (B i w)) =
        (U.basisAllAllowedGrading C Q).blockProj i 0
          (C i (fun c r ↦ w (positions.symm ⟨c, r⟩))) := by sorry
