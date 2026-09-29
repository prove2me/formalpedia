-- Prove2me | Theorems.Thm_mme_little_endian_MM_kronPow_tensor
-- name    : mme_little_endian_MM_kronPow_tensor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T05:17:06.690615+00:00
-- url     : https://prove2.me/theorems/27cf644f-dd88-432d-a379-84c38edd4b4d
-- title:
--   Exact little-endian flattening of matrix-multiplication tensor powers
-- statement:
--   Let \(\langle n,m,p\rangle\) denote the matrix-multiplication tensor. For every nonnegative integer \(r\), the explicit little-endian coordinate maps send its \(r\)-fold Kronecker power exactly to the standard tensor of dimensions \(n^r,m^r,p^r\):\n\n$$\n\operatorname{map}(F_r)\bigl(\langle n,m,p\rangle^{\otimes r}\bigr)=\langle n^r,m^r,p^r\rangle.\n$$\n\nThe maps retain the coordinate order of tensor-power words, placing position zero in the least-significant digit. This coordinate-sensitive form is needed to identify prescribed CW channel words after flattening.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section 6.3 and Appendix A, https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_little_endian_MM_power_flatten

open PiTensorProduct TensorProduct BigOperators
open MME
open MME.DWZFineChannel

universe u

set_option autoImplicit false

theorem mme_little_endian_MM_kronPow_tensor
    (K : Type u) [Field K] (n m p r : ℕ) :
    PiTensorProduct.map (littleEndianPowerMaps K n m p r)
        ((MMObj K n m p).kronPow r).t =
      (MMObj K (n ^ r) (m ^ r) (p ^ r)).t := by
  sorry
