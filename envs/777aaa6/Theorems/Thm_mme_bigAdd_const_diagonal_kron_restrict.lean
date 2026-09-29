-- Prove2me | Theorems.Thm_mme_bigAdd_const_diagonal_kron_restrict
-- name    : mme_bigAdd_const_diagonal_kron_restrict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T08:42:18.784274+00:00
-- url     : https://prove2.me/theorems/ec2d01f1-6f56-4863-b450-eade52a2cade
-- title:
--   Diagonal pairing of two constant tensor direct sums
-- statement:
--   For tensor objects $X$ and $Y$, the direct sum of $k$ diagonal copies of $X\otimes Y$ is a restriction of the Kronecker product of $k$ copies of $X$ with $k$ copies of $Y$. Equivalently, one may retain the $k$ matching label pairs and zero all $k^2-k$ off-diagonal pairs. This is the finite direct-sum pairing used when the two cyclic halves of a six-symmetrization must share the same outer hash label.
-- source:
--   Standard direct-sum and Kronecker-product functoriality in Strassen's tensor restriction preorder; used in Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, Definition 3.3.

import Definitions.Def_mme_rank_bridge

open MME

universe u

set_option autoImplicit false

theorem mme_bigAdd_const_diagonal_kron_restrict
    {K : Type u} [Field K] {d : ℕ} (hd : 1 < d)
    (X Y : TensorObj K d) (k : ℕ) :
    TensorObj.Restrict
      (TensorObj.bigAdd (fun _ : Fin k ↦ TensorObj.kron X Y))
      (TensorObj.kron
        (TensorObj.bigAdd (fun _ : Fin k ↦ X))
        (TensorObj.bigAdd (fun _ : Fin k ↦ Y))) := by
  sorry
