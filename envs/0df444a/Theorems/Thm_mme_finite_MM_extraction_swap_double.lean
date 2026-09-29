-- Prove2me | Theorems.Thm_mme_finite_MM_extraction_swap_double
-- name    : mme_finite_MM_extraction_swap_double
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T12:33:12.386583+00:00
-- url     : https://prove2.me/theorems/bbf4f645-0849-4eb3-b091-082f568f6871
-- title:
--   Swap-and-double a finite cyclic MM extraction
-- statement:
--   If the cyclic symmetrization of a tensor contains a direct sum of k matrix-multiplication tensors with dimensions (a_i,b_i,c_i), then its six-symmetrization contains all k² ordered products with dimensions (a_i c_j,b_i b_j,c_i a_j). The second family is obtained by swapping the first two tensor modes, and every Cartesian pair is retained.
-- source:
--   Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, Definition 3.3; standard direct-sum and Kronecker-product functoriality for matrix-multiplication tensors.

import Definitions.Def_mme_six_symmetrized_tau_value

open MME

universe u

set_option autoImplicit false

theorem mme_finite_MM_extraction_swap_double
    {K : Type u} [Field K] {T : TensorObj K 3} {k : ℕ}
    (a b c : Fin k → ℕ)
    (hrestrict : TensorObj.Restrict
      (TensorObj.bigAdd (fun j ↦ MMObj K (a j) (b j) (c j)))
      (cyclicSymmetrization T)) :
    TensorObj.Restrict
      (TensorObj.bigAdd (fun r : Fin (k * k) ↦
        let ij := finProdFinEquiv.symm r
        MMObj K
          (a ij.1 * c ij.2)
          (b ij.1 * b ij.2)
          (c ij.1 * a ij.2)))
      (sixSymmetrization T) := by
  sorry
