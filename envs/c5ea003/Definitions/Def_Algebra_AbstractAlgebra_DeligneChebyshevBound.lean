-- Prove2me | Definitions.Def_Algebra_AbstractAlgebra_DeligneChebyshevBound
-- name    : Algebra_AbstractAlgebra_DeligneChebyshevBound
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T08:04:49.484189+00:00
-- url     : https://prove2.me/theorems/c6633e42-0a44-4bb4-a51e-5785eab8c423
-- title:
--   Aether Catalog definitions — Algebra_AbstractAlgebra_DeligneChebyshevBound
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.AbstractAlgebra.DeligneChebyshevBound`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/AbstractAlgebra/DeligneChebyshevBound.lean by skeleton subtraction
import Mathlib

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

namespace DeligneChebyshev

/-- Evaluation of the `k`-th Chebyshev polynomial of the second kind at a real point. -/
noncomputable def Uval (k : ℕ) (x : ℝ) : ℝ :=
  (Polynomial.Chebyshev.U ℝ (k : ℤ)).eval x






/-! ## Triple correlation sums -/

/-- The triple correlation sum `∑_{n ≤ N} f(n) g(n+1) h(n+2)`. -/
def triple_sum (f g h : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (N + 1), f n * g (n + 1) * h (n + 2)



end DeligneChebyshev


