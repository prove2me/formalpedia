-- Prove2me | Theorems.Thm_DeligneChebyshev_U_deligne_bound
-- name    : DeligneChebyshev.U_deligne_bound
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:29:53.643929+00:00
-- url     : https://prove2.me/theorems/71ccf88c-f35b-4995-89b7-d3e80dd80eae
-- title:
--   Core theorem — the Deligne bound.
-- statement:
--   **Core theorem — the Deligne bound.** For `x ∈ [-1,1]`, `|U_k(x)| ≤ k + 1`.
--
--   ```lean
--   theorem DeligneChebyshev.U_deligne_bound(k : ℕ) (x : ℝ) (hx : x ∈ Icc (-1 : ℝ) 1) :
--       |Uval k x| ≤ (k + 1 : ℕ) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/AbstractAlgebra/DeligneChebyshevBound.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/AbstractAlgebra/DeligneChebyshevBound.lean#L81

-- Thm stub generated from Algebra/AbstractAlgebra/DeligneChebyshevBound.lean
import Mathlib
import Definitions.Def_Algebra_AbstractAlgebra_DeligneChebyshevBound

/-!
# The Deligne bound for Chebyshev `U`-polynomials and triple correlation sums

This file proves the (elementary) "Deligne bound" for the Chebyshev polynomials of the
second kind `U_k` on the interval `[-1, 1]`:
`|U_k(x)| ≤ k + 1` for all `x ∈ [-1, 1]`.

The name refers to the analogy with Deligne's bounds for the eigenvalues of Frobenius
(equivalently, for Hecke eigenvalues / Kloosterman-type sums), where the relevant local
factors are exactly Chebyshev `U`-polynomials evaluated on `[-1,1]`.

We also record the immediate application to **triple correlation sums**: any sum
`∑_{n ≤ N} f(n) g(n+1) h(n+2)` of three sequences bounded by `1` in absolute value is
bounded by `N + 1`, and this bound is sharp.

The Chebyshev polynomial is `Polynomial.Chebyshev.U ℝ k`, evaluated via `Polynomial.eval`.
We package this as a real-valued function `Uval k x`.
-/

open Real Set
open scoped BigOperators

open DeligneChebyshev

theorem DeligneChebyshev.U_deligne_bound(k : ℕ) (x : ℝ) (hx : x ∈ Icc (-1 : ℝ) 1) :
    |Uval k x| ≤ (k + 1 : ℕ) := by sorry
