-- Prove2me | Theorems.Thm_mme_basisZAllowedSubtensor_restrict_MM_oneOne_of_exact_router
-- name    : mme_basisZAllowedSubtensor_restrict_MM_oneOne_of_exact_router
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T07:02:25.471942+00:00
-- url     : https://prove2.me/theorems/333ad9d6-5b9c-4907-ae08-c0aaa429e633
-- title:
--   Exact allowed-basis descent for one-by-one rectangular matrix multiplication
-- statement:
--   Let $T$ be a three-tensor over a field $K$, with a named basis $b_i$ in its third mode. Suppose an exact restriction map sends $T$ to the rectangular matrix-multiplication tensor $\langle 1,1,P\rangle$, and sends every $b_i$ to a distinct standard third-mode channel indexed by an injection $c:I\hookrightarrow[P]$. For any predicate $A$ selecting basis labels, the literal third-mode basis projection of $T$ to the selected labels restricts to
--
--   $$
--   \langle 1,1,|\{i\in I:A(i)\}|\rangle.
--   $$
--
--   The statement keeps the selected dimension exact. It is the reusable finite coordinate-selection step for equal-multiplicity rectangular constituents in laser-method component powers.
-- source:
--   Elementary coordinate projection for matrix-multiplication tensors; used in Duan--Wu--Zhou, Faster Matrix Multiplication via Asymmetric Hashing, Section 6.3 rectangular Table-2 constituents, arXiv:2210.10173v5.

import Mathlib
import Definitions.Def_mme_basis_z_allowed_projection

open PiTensorProduct
open MME Module

universe u

set_option autoImplicit false

theorem mme_basisZAllowedSubtensor_restrict_MM_oneOne_of_exact_router
    {K : Type u} [Field K] {T : TensorObj K 3}
    {I : Type u} [Fintype I] [DecidableEq I]
    (bZ : Basis I K (T.V 2)) (allowed : I → Prop)
    [DecidablePred allowed] {P : ℕ} (coord : I ↪ Fin P)
    (router : ∀ s, T.V s →ₗ[K] (MMObj K 1 1 P).V s)
    (hrouter : PiTensorProduct.map router T.t = (MMObj K 1 1 P).t)
    (hrouterZ : ∀ i,
      router 2 (bZ i) =
        (Pi.single (coord i, (0 : Fin 1)) 1 : Fin P × Fin 1 → K)) :
    TensorObj.Restrict
      (MMObj K 1 1 (Nat.card {i : I // allowed i}))
      (T.basisZAllowedSubtensor bZ allowed) := by
  sorry
