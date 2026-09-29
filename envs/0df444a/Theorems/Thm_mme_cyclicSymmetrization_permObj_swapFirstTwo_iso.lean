-- Prove2me | Theorems.Thm_mme_cyclicSymmetrization_permObj_swapFirstTwo_iso
-- name    : mme_cyclicSymmetrization_permObj_swapFirstTwo_iso
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T21:56:10.215657+00:00
-- url     : https://prove2.me/theorems/a63d6607-d214-47cd-a286-466758ed432e
-- title:
--   Cyclic symmetrization commutes with a mode transposition
-- statement:
--   For every order-three tensor, cyclically symmetrizing after exchanging the first two tensor modes is tensor-isomorphic to exchanging those modes after cyclic symmetrization.  Conjugation by the transposition exchanges the two nontrivial cyclic rotations, and Kronecker product is commutative up to tensor isomorphism.
-- source:
--   Standard dihedral symmetry of the three cyclic mode rotations; used in A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, Section 5; https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Definitions.Def_mme_cyclicSymmetrization_public_perm
import Definitions.Def_mme_six_symmetrized_tau_value

open MME

universe u

set_option autoImplicit false

theorem mme_cyclicSymmetrization_permObj_swapFirstTwo_iso
    {K : Type u} [Field K] (X : TensorObj K 3) :
    TensorObj.Isomorphic
      (cyclicSymmetrization (TensorObj.permObj swapFirstTwoPerm X))
      (TensorObj.permObj swapFirstTwoPerm (cyclicSymmetrization X)) := by
  sorry
