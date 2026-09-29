-- Prove2me | Theorems.Thm_trace_rank_one_outer_product_self_eq_norm_sq
-- name    : trace_rank_one_outer_product_self_eq_norm_sq
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-06-24T00:01:30.150427+00:00
-- url     : https://prove2.me/theorems/0753beef-c09e-4361-9946-8b1b0cf38c4b
-- statement:
--   **Trace of the self outer product equals `||y||^2`.** `tr(y(x)y) = sum_i y_i^2`. Proof: the diagonal of `vecMulVec y y` is `i |-> y_i y_i = y_i^2`, and the trace is its sum.
-- source:
--   Rudelson, 'Random vectors in the isotropic position', J. Funct. Anal. 164 (1999), Thm 1 pp.3-6; van Handel, 'Structured Random Matrices', arXiv:1610.05200 Sec. 3 (Lemma 3.5); Candes-Recht 2009 (arXiv:0805.4471) Sec. 4.2 eq (4.9) p.18. These are the rank-one (outer-product) operator identities used by the noncommutative-Khintchine step of Rudelson's selection lemma; the rank-one summands are X_c = y_c (x) y_c on the Hilbert-Schmidt space, and the Gram square collapses by (yy*)^2 = ||y||^2 (yy*).

import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic
open scoped BigOperators Matrix

theorem trace_rank_one_outer_product_self_eq_norm_sq {d : Nat} (y : Fin d → Real) : Matrix.trace (Matrix.vecMulVec y y) = ∑ i, (y i) ^ 2 := by sorry
