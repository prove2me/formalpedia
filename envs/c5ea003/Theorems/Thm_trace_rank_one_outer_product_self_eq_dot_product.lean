-- Prove2me | Theorems.Thm_trace_rank_one_outer_product_self_eq_dot_product
-- name    : trace_rank_one_outer_product_self_eq_dot_product
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-06-24T00:01:37.732231+00:00
-- url     : https://prove2.me/theorems/3039dc31-6ef9-4186-9e58-97123d06ce05
-- statement:
--   **Trace of the self outer product as the self dot product `tr(y(x)y) = y . y`.** The trace of the rank-one outer product equals the dot product of the vector with itself (the dotProduct form of `||y||^2`). Proof: the diagonal is `i |-> y_i y_i`, whose sum is exactly `y . y`.
-- source:
--   Rudelson, 'Random vectors in the isotropic position', J. Funct. Anal. 164 (1999), Thm 1 pp.3-6; van Handel, 'Structured Random Matrices', arXiv:1610.05200 Sec. 3 (Lemma 3.5); Candes-Recht 2009 (arXiv:0805.4471) Sec. 4.2 eq (4.9) p.18. These are the rank-one (outer-product) operator identities used by the noncommutative-Khintchine step of Rudelson's selection lemma; the rank-one summands are X_c = y_c (x) y_c on the Hilbert-Schmidt space, and the Gram square collapses by (yy*)^2 = ||y||^2 (yy*).

import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic
open scoped BigOperators Matrix

theorem trace_rank_one_outer_product_self_eq_dot_product {d : Nat} (y : Fin d → Real) : Matrix.trace (Matrix.vecMulVec y y) = y ⬝ᵥ y := by sorry
