-- Prove2me | Theorems.Thm_sum_rank_one_outer_product_square_collapse
-- name    : sum_rank_one_outer_product_square_collapse
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-06-24T00:01:08.172159+00:00
-- url     : https://prove2.me/theorems/f76d68af-0045-4e13-a6f9-8811e7fd9a4c
-- statement:
--   **Gram-square collapse for a family of rank-one tensors.** Summing the rank-one square collapse over a finite family: `sum_c (y_c (x) y_c)^2 = sum_c ||y_c||^2 . (y_c (x) y_c)`. This is the `sum X_c^2 = sum ||y_c||^2 (y_c (x) y_c)` step of Rudelson's NC-Khintchine bound, immediately before the PSD-monotone domination by `max_c ||y_c||^2 . sum (y_c (x) y_c)`. Proof: termwise application of the rank-one square collapse `(yy*)^2 = ||y||^2 (yy*)`.
-- source:
--   Rudelson, 'Random vectors in the isotropic position', J. Funct. Anal. 164 (1999), Thm 1 pp.3-6; van Handel, 'Structured Random Matrices', arXiv:1610.05200 Sec. 3 (Lemma 3.5); Candes-Recht 2009 (arXiv:0805.4471) Sec. 4.2 eq (4.9) p.18. These are the rank-one (outer-product) operator identities used by the noncommutative-Khintchine step of Rudelson's selection lemma; the rank-one summands are X_c = y_c (x) y_c on the Hilbert-Schmidt space, and the Gram square collapses by (yy*)^2 = ||y||^2 (yy*).

import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic
open scoped BigOperators Matrix

theorem sum_rank_one_outer_product_square_collapse {d : Nat} {iota : Type*} (s : Finset iota) (y : iota → Fin d → Real) : ∑ c ∈ s, (Matrix.vecMulVec (y c) (y c) * Matrix.vecMulVec (y c) (y c)) = ∑ c ∈ s, (y c ⬝ᵥ y c) • Matrix.vecMulVec (y c) (y c) := by sorry
