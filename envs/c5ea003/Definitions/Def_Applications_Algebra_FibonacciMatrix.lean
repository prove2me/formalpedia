-- Prove2me | Definitions.Def_Applications_Algebra_FibonacciMatrix
-- name    : Applications_Algebra_FibonacciMatrix
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:31:38.539725+00:00
-- url     : https://prove2.me/theorems/6c0177d8-69c3-4811-a3d8-0b479a42426a
-- title:
--   Aether Catalog definitions — Applications_Algebra_FibonacciMatrix
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.Algebra.FibonacciMatrix`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/Algebra/FibonacciMatrix.lean by skeleton subtraction
import Mathlib

/-! # The Fibonacci `Q`-matrix, Cassini's identity, and Vajda's identity

Domain: Number Theory / Applications (a matrix-theoretic companion to the catalog's
Fibonacci entry-point theory in `Catalog/Applications/FibonacciEntryPoints.lean` and
`Catalog/Applications/FibonacciApparitionLattice.lean`).

The catalog develops Fibonacci divisibility through the *gcd bridge* `Nat.fib_gcd`
and the law of apparition.  This file installs the complementary, *multiplicative*
backbone: the classical `Q`-matrix

```
Q = !![1, 1; 1, 0]
```

whose powers read off consecutive Fibonacci numbers.  From a single structural lemma
(`fib_Q_pow`) we obtain three classical identities by pure linear algebra — taking
*determinants* gives Cassini, and *block/entry comparison of matrix products* gives the
far more general Vajda identity, from which Catalan's identity follows as a one-line
specialization.

Main results:
* `fib_Q_pow`       — `Q ^ (n+1) = !![F(n+2), F(n+1); F(n+1), F(n)]` (over `ℤ`).
* `fib_cassini`     — `F(n+2)·F(n) − F(n+1)² = (−1)^(n+1)` via `det (Q^(n+1)) = (det Q)^(n+1)`.
* `fib_vajda`       — `F(n+i)·F(n+j) − F(n)·F(n+i+j) = (−1)^n · F(i)·F(j)` (Vajda's identity).
* `fib_catalan`     — `F(n+r)² − F(n)·F(n+2r) = (−1)^n · F(r)²` (Catalan, `i = j = r`).

These complement the entry-point (additive/divisibility) viewpoint of the catalog with the
matrix (multiplicative/identity) viewpoint, and Cassini's `±1` determinant is exactly the
reason consecutive Fibonacci numbers are coprime — the seed fact underlying the apparition
theory.
-/

namespace FibonacciMatrix

open Matrix

/-- The Fibonacci `Q`-matrix `!![1,1;1,0]` over `ℤ`. -/
def Q : Matrix (Fin 2) (Fin 2) ℤ := !![1, 1; 1, 0]

/-
!-- Induction on `n`: the base case is `Q^1 = Q`, and the step multiplies by `Q` on the
right and uses `F(n+3) = F(n+1) + F(n+2)` (`Nat.fib_add_two`) to fold the entries. -- !--

**The `Q`-matrix power law.** `Q^(n+1)` has the four consecutive Fibonacci numbers
`F(n+2), F(n+1), F(n+1), F(n)` as its entries.
-/

/-
!-- `det` is multiplicative, so `det (Q^(n+1)) = (det Q)^(n+1) = (-1)^(n+1)`; evaluating the
determinant of the explicit matrix from `fib_Q_pow` via `Matrix.det_fin_two` gives the LHS. -- !--

**Cassini's identity.** For every `n`, `F(n+2)·F(n) − F(n+1)² = (−1)^(n+1)`.
-/

/-
!-- Both sides are degree-2 polynomials in the entries of `Q^n`; expand `F(n+i)`, `F(n+j)`
and `F(n+i+j)` with the addition formula `Nat.fib_add` (`F(a+b+1)=F(a)F(b)+F(a+1)F(b+1)`)
in terms of `F(n), F(n+1)` and `F(i±), F(j±)`, then collapse the cross terms using
Cassini `F(n+1)² − F(n)F(n+2) = (−1)^n`. -- !--

**Vajda's identity.** For all `n, i, j`,
`F(n+i)·F(n+j) − F(n)·F(n+i+j) = (−1)^n · F(i)·F(j)`.

This single identity contains Cassini (`i = j = 1`), Catalan (`i = j = r`), and
d'Ocagne's identity (after reindexing) as special cases.
-/

/-
!-- Specialize Vajda's identity at `i = j = r` and simplify `n + r + r = n + 2r`. -- !--

**Catalan's identity.** For all `n, r`,
`F(n+r)² − F(n)·F(n+2r) = (−1)^n · F(r)²`.
-/

end FibonacciMatrix


