-- Prove2me | Theorems.Thm_mme_MMObj_cyclicSymmetrization_iso
-- name    : mme_MMObj_cyclicSymmetrization_iso
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-03T00:06:45.111362+00:00
-- url     : https://prove2.me/theorems/01d527c5-1516-4e91-a2d4-2bfbde86a0ce
-- title:
--   The cyclic symmetrization of a matrix-multiplication tensor is square
-- statement:
--   For a field $K$, cyclically symmetrizing the matrix-multiplication tensor $\langle n,m,p\rangle$ produces a square matrix-multiplication tensor of side length $nmp$:
--
--   $$
--   \operatorname{cyc}(\langle n,m,p\rangle)\cong\langle nmp,nmp,nmp\rangle.
--   $$
--
--   Indeed, the two cyclic mode permutations have shapes $\langle p,n,m\rangle$ and $\langle m,p,n\rangle$, and Kronecker multiplication multiplies the three dimensions coordinatewise. This identity supplies the elementary cyclic values of the rectangular components in the Davie--Stothers profile.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), symmetric-value convention preceding Lemma 5.1, pp. 364--365; https://www.maths.ed.ac.uk/~sandy/a11164.pdf. The tensor identity also follows directly from multiplicativity and cyclic invariance of matrix-multiplication tensors.

import Mathlib.Tactic
import Definitions.Def_mme_CW_coupled_value
import Definitions.Def_mme_cyclicSymmetrization_public_perm
import Definitions.Def_mme_mmobj_mul
import Theorems.Thm_mme_MMObj_permObj_cyclic_sq

open MME

universe u

set_option autoImplicit false

theorem mme_MMObj_cyclicSymmetrization_iso
    {K : Type u} [Field K] (n m p : ℕ) :
    TensorObj.Isomorphic
      (cyclicSymmetrization (MMObj K n m p))
      (MMObj K (n * m * p) (n * m * p) (n * m * p)) := by
  sorry
