-- Prove2me | Theorems.Thm_rank_one_outer_product_square_collapse
-- name    : rank_one_outer_product_square_collapse
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-06-23T23:45:15.298779+00:00
-- url     : https://prove2.me/theorems/da405ca6-c600-4b94-b249-d962999a471f
-- statement:
--   **Rank-one square collapse `(yy*)^2 = ||y||^2 (yy*)`.** For the rank-one outer product `y (x) y = vecMulVec y y`, its matrix square equals the scalar `||y||^2 = y . y` times itself: `(y(x)y)(y(x)y) = (y . y) . (y(x)y)`. This is the algebraic identity that makes the Gram square of the rank-one tensor operators collapse in Rudelson's noncommutative-Khintchine selection lemma. Proof: `Matrix.vecMulVec_mul_vecMulVec` gives `vecMulVec y y * vecMulVec y y = vecMulVec y ((y . y) . y)`, then entrywise `ring`.
-- source:
--   Rudelson, 'Random vectors in the isotropic position', J. Funct. Anal. 164 (1999), Thm 1 pp.3-6; van Handel, 'Structured Random Matrices', arXiv:1610.05200 Sec. 3 (Lemma 3.5); Candes-Recht 2009 (arXiv:0805.4471) Sec. 4.2 eq (4.9) p.18. These are the rank-one (outer-product) operator identities used by the noncommutative-Khintchine step of Rudelson's selection lemma; the rank-one summands are X_c = y_c (x) y_c on the Hilbert-Schmidt space, and the Gram square collapses by (yy*)^2 = ||y||^2 (yy*).

import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic
open scoped BigOperators Matrix

theorem rank_one_outer_product_square_collapse {d : Nat} (y : Fin d → Real) : Matrix.vecMulVec y y * Matrix.vecMulVec y y = (y ⬝ᵥ y) • Matrix.vecMulVec y y := by sorry
