-- Prove2me | Theorems.Thm_trace_rank_one_outer_product_mul_eq_inner_sq
-- name    : trace_rank_one_outer_product_mul_eq_inner_sq
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-06-24T00:01:16.068246+00:00
-- url     : https://prove2.me/theorems/8c88ea17-cd36-4ef0-8416-1d60c1171488
-- statement:
--   **Gram trace identity `tr((y(x)y)(z(x)z)) = <y,z>^2`.** The trace of a product of two rank-one outer products equals the square of the inner product. This is the identity the van Handel Gram recursion uses to expand traces of products of rank-one tensor operators. Proof: `Matrix.vecMulVec_mul_vecMulVec` reduces the product to `vecMulVec y ((y . z) . z)`, factor the scalar `(y . z)` out of the trace sum, and recognize the residual sum as `y . z`.
-- source:
--   Rudelson, 'Random vectors in the isotropic position', J. Funct. Anal. 164 (1999), Thm 1 pp.3-6; van Handel, 'Structured Random Matrices', arXiv:1610.05200 Sec. 3 (Lemma 3.5); Candes-Recht 2009 (arXiv:0805.4471) Sec. 4.2 eq (4.9) p.18. These are the rank-one (outer-product) operator identities used by the noncommutative-Khintchine step of Rudelson's selection lemma; the rank-one summands are X_c = y_c (x) y_c on the Hilbert-Schmidt space, and the Gram square collapses by (yy*)^2 = ||y||^2 (yy*).

import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic
open scoped BigOperators Matrix

theorem trace_rank_one_outer_product_mul_eq_inner_sq {d : Nat} (y z : Fin d → Real) : Matrix.trace (Matrix.vecMulVec y y * Matrix.vecMulVec z z) = (y ⬝ᵥ z) ^ 2 := by sorry
