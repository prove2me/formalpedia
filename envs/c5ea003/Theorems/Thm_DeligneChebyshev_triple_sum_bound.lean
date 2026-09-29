-- Prove2me | Theorems.Thm_DeligneChebyshev_triple_sum_bound
-- name    : DeligneChebyshev.triple_sum_bound
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:30:06.813928+00:00
-- url     : https://prove2.me/theorems/10ce6990-c216-4e3f-bbf5-d8a1ba6525a8
-- title:
--   Triple correlation envelope.
-- statement:
--   **Triple correlation envelope.** Three sequences bounded by `1` give a sum bounded by `N+1`.
--
--   ```lean
--   theorem DeligneChebyshev.triple_sum_bound(f g h : ℕ → ℝ)
--       (hf : ∀ n, |f n| ≤ 1) (hg : ∀ n, |g n| ≤ 1) (hh : ∀ n, |h n| ≤ 1) (N : ℕ) :
--       |triple_sum f g h N| ≤ (N + 1 : ℕ) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/AbstractAlgebra/DeligneChebyshevBound.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/AbstractAlgebra/DeligneChebyshevBound.lean#L126

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







/-! ## Triple correlation sums -/

theorem DeligneChebyshev.triple_sum_bound(f g h : ℕ → ℝ)
    (hf : ∀ n, |f n| ≤ 1) (hg : ∀ n, |g n| ≤ 1) (hh : ∀ n, |h n| ≤ 1) (N : ℕ) :
    |triple_sum f g h N| ≤ (N + 1 : ℕ) := by sorry
