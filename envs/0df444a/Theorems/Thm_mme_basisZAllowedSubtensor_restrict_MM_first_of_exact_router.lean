-- Prove2me | Theorems.Thm_mme_basisZAllowedSubtensor_restrict_MM_first_of_exact_router
-- name    : mme_basisZAllowedSubtensor_restrict_MM_first_of_exact_router
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T07:09:04.795296+00:00
-- url     : https://prove2.me/theorems/037770a7-6aee-4c82-bf90-7a96ec14edb6
-- title:
--   Exact allowed-basis descent for first-mode rectangular matrix multiplication
-- statement:
--   Let $T$ be a three-tensor over a field $K$, with a named basis $b_i$ in its third mode. Suppose an exact restriction map sends $T$ to $\langle P,1,1\rangle$, and sends every $b_i$ to a distinct standard third-mode channel indexed by an injection $c:I\hookrightarrow[P]$. For any predicate $A$ selecting basis labels, the literal third-mode basis projection of $T$ to the selected labels restricts to
--
--   $$
--   \langle |\{i\in I:A(i)\}|,1,1\rangle.
--   $$
--
--   This is the mode-rotated companion of the exact one-by-one rectangular selection theorem and retains the selected dimension exactly.
-- source:
--   Elementary coordinate projection for matrix-multiplication tensors; used in Duan--Wu--Zhou, Faster Matrix Multiplication via Asymmetric Hashing, Section 6.3 rectangular Table-2 constituents, arXiv:2210.10173v5.

import Mathlib
import Definitions.Def_mme_basis_z_allowed_projection

open PiTensorProduct
open MME Module

universe u

set_option autoImplicit false

theorem mme_basisZAllowedSubtensor_restrict_MM_first_of_exact_router
    {K : Type u} [Field K] {T : TensorObj K 3}
    {I : Type u} [Fintype I] [DecidableEq I]
    (bZ : Basis I K (T.V 2)) (allowed : I → Prop)
    [DecidablePred allowed] {P : ℕ} (coord : I ↪ Fin P)
    (router : ∀ s, T.V s →ₗ[K] (MMObj K P 1 1).V s)
    (hrouter : PiTensorProduct.map router T.t = (MMObj K P 1 1).t)
    (hrouterZ : ∀ i,
      router 2 (bZ i) =
        (Pi.single ((0 : Fin 1), coord i) 1 : Fin 1 × Fin P → K)) :
    TensorObj.Restrict
      (MMObj K (Nat.card {i : I // allowed i}) 1 1)
      (T.basisZAllowedSubtensor bZ allowed) := by
  sorry
