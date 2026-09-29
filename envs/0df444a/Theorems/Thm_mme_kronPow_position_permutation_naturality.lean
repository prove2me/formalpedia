-- Prove2me | Theorems.Thm_mme_kronPow_position_permutation_naturality
-- name    : mme_kronPow_position_permutation_naturality
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T08:53:56.34391+00:00
-- url     : https://prove2.me/theorems/438bbd1b-579b-4933-9d17-ac9b016947b2
-- title:
--   Tensor-power position permutations commute with basis-aligned maps
-- statement:
--   Let $T$ and $S$ be tensors over a field, fix one mode, and choose bases of the corresponding mode spaces. Suppose a linear map $f$ sends every selected source basis vector $b_a$ to the target basis vector $c_{\sigma(a)}$. For every tensor-power exponent $n$ and every permutation $e$ of its $n$ positions, let $P_T(e)$ and $P_S(e)$ be the linear automorphisms induced by applying the same position reindexing to the canonical word bases. Then the induced tensor-power map $f^{\otimes n}$ commutes with these reindexings:
--
--   $$
--   f^{\otimes n} \circ P_T(e)=P_S(e)\circ f^{\otimes n}.
--   $$
--
--   This naturality square is the reusable linear-algebra interface needed to realize the common position shuffle in Duan--Wu--Zhou Claim 5.9 on both an ambient tensor power and its basis-labelled restricted small blocks. It includes the zero-power case.
--
--   **Formalization Note** Tensor powers use the recursively parenthesized `TensorObj.kronPow` representation; the equality is an exact equality of linear maps, not merely an isomorphism of quotient tensor objects.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Definition 5.7 and Claims 5.8--5.9, PDF pp. 49--50 / printed pp. 48--49; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_kronPow_position_permutation_linear_data

open MME MME.TensorObj TensorProduct Module

universe u

set_option autoImplicit false

theorem mme_kronPow_position_permutation_naturality
    {K : Type u} [Field K] {d : ℕ}
    {T S : TensorObj K d} (i : Fin d)
    {ι κ : Type u}
    (b : Basis ι K (T.V i)) (c : Basis κ K (S.V i))
    (f : T.V i →ₗ[K] S.V i) (σ : ι → κ)
    (hf : ∀ a, f (b a) = c (σ a))
    (n : ℕ) (e : Equiv.Perm (Fin n)) :
    (kronPowModeMap i f n).comp
        (kronPowModePositionEquiv T i b n e).toLinearMap =
      (kronPowModePositionEquiv S i c n e).toLinearMap.comp
        (kronPowModeMap i f n) := by
  sorry
