-- Prove2me | Theorems.Thm_frobenius_sq_rank_one_outer_product_self_eq_norm_sq_sq
-- name    : frobenius_sq_rank_one_outer_product_self_eq_norm_sq_sq
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-06-24T00:01:44.849681+00:00
-- url     : https://prove2.me/theorems/47fbde29-261d-4249-99ad-0d39b1fc4763
-- statement:
--   **Frobenius-norm-squared of the self outer product equals `||y||^4`.** `sum_{ij} (y_i y_j)^2 = (sum_i y_i^2)^2`. Proof: each row `i` contributes `y_i^2 . sum_j y_j^2`; summing over `i` factors as `(sum_i y_i^2)(sum_j y_j^2) = ||y||^4`.
-- source:
--   Rudelson, 'Random vectors in the isotropic position', J. Funct. Anal. 164 (1999), Thm 1 pp.3-6; van Handel, 'Structured Random Matrices', arXiv:1610.05200 Sec. 3 (Lemma 3.5); Candes-Recht 2009 (arXiv:0805.4471) Sec. 4.2 eq (4.9) p.18. These are the rank-one (outer-product) operator identities used by the noncommutative-Khintchine step of Rudelson's selection lemma; the rank-one summands are X_c = y_c (x) y_c on the Hilbert-Schmidt space, and the Gram square collapses by (yy*)^2 = ||y||^2 (yy*).

import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic
open scoped BigOperators Matrix

theorem frobenius_sq_rank_one_outer_product_self_eq_norm_sq_sq {d : Nat} (y : Fin d → Real) : ∑ i, ∑ j, (Matrix.vecMulVec y y i j) ^ 2 = (∑ i, (y i) ^ 2) ^ 2 := by sorry
