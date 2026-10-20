-- Prove2me | Theorems.Thm_mme_complex_arithmetic_omega_le_matMulExp
-- name    : mme_complex_arithmetic_omega_le_matMulExp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T19:36:51.378657+00:00
-- url     : https://prove2.me/theorems/95414445-79cc-4a2c-b90a-27230c0c9c07
-- title:
--   Tensor-rank campaign bounds imply complex arithmetic-circuit bounds
-- statement:
--   The arithmetic-circuit exponent for square matrix multiplication over the complex numbers is at most the tensor-rank exponent used by the matrix-multiplication campaign:
--
--   $$\omega_{\mathrm{arith},\mathbb C}\le\omega_{\mathrm{rank},\mathbb C}.$$
--
--   The left side uses the published division-free straight-line-program model: inputs and constants are free, and each addition, subtraction, or multiplication costs one. Admissibility requires a correct program at every positive size, with one uniform constant for each positive exponent slack. The right side is the infimum, over integer sizes at least two, of the logarithm of the exact matrix-multiplication tensor rank divided by the logarithm of the size.
--
--   Consequently, every non-strict upper bound on the campaign exponent over ℂ also bounds the arithmetic-circuit exponent; every strict upper bound transfers as well. A campaign theorem quantified over all fields is first specialized to ℂ. This theorem asserts the direction needed to transfer upper bounds, not equality of the two exponents.
-- source:
--   Strassen rank-to-arithmetic block-recursion theorem; see ACM 270 lecture notes (Kueng and Tropp, 2019), Lecture 12, §3.2, Theorem 3.2, https://iqim.caltech.edu/wp-content/uploads/2019/08/ACM270_complete_lecture_notes.pdf (PDF p. 96). Lean construction adapted from the accepted Prove2me proof b57d8d9d-7446-4954-b328-36fff2fa94e4 of OAI.MatrixMultiplication.complex_omega_le_nine_quarters, itself ported from openai/math revision adc7f1241b42e322a6451854ab7e4b4c146bf78a, OAI/LinearAlgebra/MatrixMultiplication/AuxiliarySeparation/Arithmetic/Exponent.lean. The new coordinate map connects that construction to MME.MMTensor and MME.tensorRank.

import Definitions.Def_mme_omega
import Definitions.Def_OAI_MatrixMultiplication_Arithmetic_omega

theorem mme_complex_arithmetic_omega_le_matMulExp :
    OAI.MatrixMultiplication.Arithmetic.omega ℂ ≤ MME.matMulExp ℂ := by sorry
