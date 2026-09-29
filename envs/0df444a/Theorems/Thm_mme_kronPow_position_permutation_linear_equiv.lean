-- Prove2me | Theorems.Thm_mme_kronPow_position_permutation_linear_equiv
-- name    : mme_kronPow_position_permutation_linear_equiv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T08:55:25.005599+00:00
-- url     : https://prove2.me/theorems/37cdc82f-34cf-4e8b-b2de-4f5603579ea7
-- title:
--   Tensor powers admit literal position-permutation automorphisms
-- statement:
--   Let $T$ be a $d$-mode tensor over a field $K$, and choose a basis $b_i$ in every mode. The resulting recursive tensor power $T^{\otimes n}$ has a canonical word basis in each mode, indexed by length-$n$ words $w$. For every permutation $e$ of the $n$ tensor positions, there are modewise linear automorphisms $P_{e,i}$ satisfying
--
--   $$
--   P_{e,i}(B_{i,w})=B_{i,w\circ e}
--   $$
--
--   and their simultaneous action fixes the tensor itself exactly:
--
--   $$
--   \left(\bigotimes_i P_{e,i}\right)\!\left(T^{\otimes n}\right)=T^{\otimes n}.
--   $$
--
--   Thus a common permutation of identical tensor-power positions is realized by explicit linear maps, not merely by a quotient-level tensor isomorphism. This is the ambient linear-algebra mechanism required for the useful-block shuffle in Duan--Wu--Zhou Claim 5.9. The statement also covers the zero tensor power.
--
--   **Formalization Note** `TensorObj.kronPow` is recursively parenthesized. The theorem gives the exact action on every canonical word-basis vector and literal equality of the mapped tensor.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Definition 5.7 and Claim 5.9, PDF pp. 49--50 / printed pp. 48--49; https://arxiv.org/abs/2210.10173. This theorem isolates the standard tensor-power permutation symmetry used in that claim.

import Definitions.Def_mme_kronPow_position_permutation_linear_data

open MME MME.TensorObj PiTensorProduct Module

universe u

set_option autoImplicit false

theorem mme_kronPow_position_permutation_linear_equiv
    {K : Type u} [Field K] {d : ℕ}
    (T : TensorObj K d) {ι : Fin d → Type u}
    (b : ∀ i, Basis (ι i) K (T.V i))
    (n : ℕ) (e : Equiv.Perm (Fin n)) :
    ∃ Φ : ∀ i : Fin d,
        (T.kronPow n).V i ≃ₗ[K] (T.kronPow n).V i,
      (∀ (i : Fin d) (w : Fin n → ι i),
        Φ i
            (kronPowModeWordBasis T i (b i) n w) =
          kronPowModeWordBasis T i (b i) n (fun r ↦ w (e r))) ∧
      PiTensorProduct.map (fun i ↦ (Φ i).toLinearMap)
          (T.kronPow n).t =
        (T.kronPow n).t := by
  sorry
