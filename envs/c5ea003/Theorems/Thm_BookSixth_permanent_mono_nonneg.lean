-- Prove2me | Theorems.Thm_BookSixth_permanent_mono_nonneg
-- name    : BookSixth.permanent_mono_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T00:32:12.246544+00:00
-- url     : https://prove2.me/theorems/7b88f2b1-a693-4dbc-8d84-5867d18b087f
-- title:
--   Chapter 37 adapter: permanent is entrywise monotone
-- statement:
--   Entrywise comparison of nonnegative real matrices is preserved by the permanent: if $0 \le A_{ij} \le B_{ij}$ for all $i,j$, then $\mathrm{perm}(A) \le \mathrm{perm}(B)$. Used to compare Latin row-extension matrices against uniform bounds in Chapter 37.
-- source:
--   Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), Chapter 37, permanent comparison adapter, p. 266. https://doi.org/10.1007/978-3-662-57265-8_37

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.permanent_mono_nonneg (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℝ)
    (hnn : ∀ i j, 0 ≤ A i j) (hle : ∀ i j, A i j ≤ B i j) :
    Matrix.permanent A ≤ Matrix.permanent B := by sorry
