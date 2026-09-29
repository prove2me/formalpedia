-- Prove2me | Theorems.Thm_rank_one_outer_product_self_symmetric
-- name    : rank_one_outer_product_self_symmetric
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-06-24T00:01:23.17304+00:00
-- url     : https://prove2.me/theorems/6f3f0f06-887b-4e83-8b3f-cb83c9020481
-- statement:
--   **Self outer product is symmetric `(y(x)y)^T = y(x)y`.** The rank-one outer product of a vector with itself is a symmetric matrix. Proof: entrywise, `(y(x)y)_{ji} = y_j y_i = y_i y_j = (y(x)y)_{ij}` by commutativity of multiplication.
-- source:
--   Rudelson, 'Random vectors in the isotropic position', J. Funct. Anal. 164 (1999), Thm 1 pp.3-6; van Handel, 'Structured Random Matrices', arXiv:1610.05200 Sec. 3 (Lemma 3.5); Candes-Recht 2009 (arXiv:0805.4471) Sec. 4.2 eq (4.9) p.18. These are the rank-one (outer-product) operator identities used by the noncommutative-Khintchine step of Rudelson's selection lemma; the rank-one summands are X_c = y_c (x) y_c on the Hilbert-Schmidt space, and the Gram square collapses by (yy*)^2 = ||y||^2 (yy*).

import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic
open scoped BigOperators Matrix

theorem rank_one_outer_product_self_symmetric {d : Nat} (y : Fin d → Real) : (Matrix.vecMulVec y y)ᵀ = Matrix.vecMulVec y y := by sorry
