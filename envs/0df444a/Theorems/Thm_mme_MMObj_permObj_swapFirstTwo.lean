-- Prove2me | Theorems.Thm_mme_MMObj_permObj_swapFirstTwo
-- name    : mme_MMObj_permObj_swapFirstTwo
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T20:37:38.952892+00:00
-- url     : https://prove2.me/theorems/da30b7e4-2bfa-4ede-89e7-54599740e628
-- title:
--   Swapping the first two modes reverses the outer matrix dimensions
-- statement:
--   For every field $K$, permuting the first two modes of the matrix-multiplication tensor $\langle n,m,p\rangle$ gives a tensor isomorphic to $\langle p,m,n\rangle$:
--
--   $$
--   (12)\cdot\langle n,m,p\rangle\cong\langle p,m,n\rangle.
--   $$
--
--   The isomorphism transposes the coordinate pair on each of the three tensor legs. This is the missing transposition identity needed to normalize the second factor in the full six-symmetrization of a rectangular matrix-multiplication tensor.
-- source:
--   Standard cyclic/transposition symmetry of the matrix-multiplication tensor; used in Duan--Wu--Zhou, Faster Matrix Multiplication via Asymmetric Hashing, Definition 3.3, arXiv:2210.10173v5.

import Mathlib.Tactic
import Definitions.Def_mme_six_symmetrized_tau_value

open PiTensorProduct BigOperators
open MME

universe u

set_option autoImplicit false

theorem mme_MMObj_permObj_swapFirstTwo
    {K : Type u} [Field K] (n m p : ℕ) :
    TensorObj.Isomorphic
      (TensorObj.permObj swapFirstTwoPerm (MMObj K n m p))
      (MMObj K p m n) := by
  sorry
