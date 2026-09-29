-- Prove2me | Theorems.Thm_mme_sixSymmetrization_MMObj_isomorphic
-- name    : mme_sixSymmetrization_MMObj_isomorphic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T20:40:20.006464+00:00
-- url     : https://prove2.me/theorems/fc8f1900-0073-43cf-97f3-51da68fbaebb
-- title:
--   Six-symmetrizing one rectangular product gives a square product of side $(nmp)^2$
-- statement:
--   Let $\langle n,m,p\rangle$ be a rectangular matrix-multiplication tensor over a field $K$. Its full six-symmetrization in the sense of Duan--Wu--Zhou is tensor-isomorphic to the square matrix-multiplication tensor
--
--   $$
--   \operatorname{Sym}_6(\langle n,m,p\rangle)\cong\langle (nmp)^2,(nmp)^2,(nmp)^2\rangle.
--   $$
--
--   The resulting product volume is $(nmp)^6$, exactly the sixth power required by the six-symmetric value normalization. This theorem is a reusable finite-tensor adapter; it makes no asymptotic or value-level replacement.
-- source:
--   Duan--Wu--Zhou, Faster Matrix Multiplication via Asymmetric Hashing, Definition 3.3 (full six-symmetrization), arXiv:2210.10173v5; standard multiplicativity and mode symmetries of matrix-multiplication tensors.

import Mathlib.Tactic
import Definitions.Def_mme_tensor_bridge
import Definitions.Def_mme_cyclicSymmetrization_public_perm
import Theorems.Thm_mme_MMObj_permObj_cyclic_sq
import Theorems.Thm_mme_MMObj_permObj_swapFirstTwo

open MME

universe u

set_option autoImplicit false

theorem mme_sixSymmetrization_MMObj_isomorphic
    {K : Type u} [Field K] (n m p : ℕ) :
    TensorObj.Isomorphic
      (sixSymmetrization (MMObj K n m p))
      (MMObj K ((n * m * p) ^ 2) ((n * m * p) ^ 2)
        ((n * m * p) ^ 2)) := by
  sorry
