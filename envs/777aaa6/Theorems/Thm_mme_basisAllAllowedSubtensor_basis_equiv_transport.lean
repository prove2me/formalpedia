-- Prove2me | Theorems.Thm_mme_basisAllAllowedSubtensor_basis_equiv_transport
-- name    : mme_basisAllAllowedSubtensor_basis_equiv_transport
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-17T08:06:12.990921+00:00
-- url     : https://prove2.me/theorems/17da345c-2ebb-4415-8544-7cb31a492f8d
-- title:
--   Basis-aware transport of all-mode coordinate projections
-- statement:
--   Let $T$ and $U$ be trilinear tensors over a field, with chosen bases in each mode. Suppose linear equivalences $E_i$ map the tensor $T$ to $U$ and send each source basis vector to its counterpart under an index bijection $p_i$. Let $P_i$ and $Q_i$ select basis vectors, with $P_i(a)$ equivalent to $Q_i(p_i(a))$.
--
--   Then the equivalences restrict to linear equivalences $F_i$ between the selected coordinate subspaces, and
--
--   $$
--   (\bigotimes_i F_i)T[P]=U[Q].
--   $$
--
--   Writing $\pi_{P,i}$ and $\pi_{Q,i}$ for the coordinate projections and $\iota_{P,i},\iota_{Q,i}$ for the inclusions, these maps satisfy
--
--   $$
--   F_i\pi_{P,i}(b_i(a))=\pi_{Q,i}(c_i(p_i(a))),\qquad
--   \iota_{Q,i}F_i=E_i\iota_{P,i}.
--   $$
--
--   This is a basis-aware linear-algebra tool for transporting the coarse restrictions and surviving-block labels used in standard-form normalization. It includes empty selected subspaces. It does not construct a DWZ component regrouping or assume that a two-way tensor restriction supplies such equivalences; the actual ambient equivalences and their basis action are explicit hypotheses.
-- source:
--   Derived linear-algebra interface for Duan–Wu–Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section 5.1, Definitions 5.2–5.5, and Section 6.1, Steps 3–4. https://arxiv.org/html/2210.10173v5#S5.SS1 . This general projection-transport lemma is not separately stated in the paper.

import Definitions.Def_mme_complete_split_profile_projection
import Definitions.Def_mme_TypeGrading_kron
import Mathlib.Algebra.Module.Submodule.Equiv

open MME Module PiTensorProduct

universe u
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem mme_basisAllAllowedSubtensor_basis_equiv_transport
    {K : Type u} [Field K] (T U : TensorObj K 3)
    {I J : Fin 3 → Type u}
    (b : ∀ i, Basis (I i) K (T.V i))
    (c : ∀ i, Basis (J i) K (U.V i))
    (e : ∀ i, T.V i ≃ₗ[K] U.V i) (p : ∀ i, I i ≃ J i)
    (hb : ∀ i a, e i (b i a) = c i (p i a))
    (ht : PiTensorProduct.map (fun i ↦ (e i).toLinearMap) T.t = U.t)
    (P : ∀ i, I i → Prop) (Q : ∀ i, J i → Prop)
    (hPQ : ∀ i a, P i a ↔ Q i (p i a)) :
    ∃ f : ∀ i, (T.basisAllAllowedGrading b P).classOf i 0 ≃ₗ[K]
        (U.basisAllAllowedGrading c Q).classOf i 0,
      PiTensorProduct.map (fun i ↦ (f i).toLinearMap)
        (T.basisAllAllowedSubtensor b P).t =
          (U.basisAllAllowedSubtensor c Q).t ∧
      (∀ i a, f i ((T.basisAllAllowedGrading b P).blockProj i 0 (b i a)) =
        (U.basisAllAllowedGrading c Q).blockProj i 0 (c i (p i a))) ∧
      (∀ i x, (f i x : U.V i) = e i (x : T.V i)) := by sorry
