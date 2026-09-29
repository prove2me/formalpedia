-- Prove2me | Definitions.Def_Novelty_ChebotarevDFT
-- name    : Novelty_ChebotarevDFT
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:08:34.659308+00:00
-- url     : https://prove2.me/theorems/3eb89710-dd39-4bf1-a721-78fed7ff48ab
-- title:
--   Aether Catalog definitions — Novelty_ChebotarevDFT
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.ChebotarevDFT`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/ChebotarevDFT.lean by skeleton subtraction
import Mathlib
/-
# Chebotarev's theorem on the roots of unity (Chebotarev–Frenkel)

Every square submatrix of the `p × p` DFT matrix `(ζ^{jk})` (`p` prime, `ζ` a primitive
`p`-th root of unity) is nonsingular.

The proof formalized here is Frenkel's argument:

* Let `A = {a i}`, `B = {b j}` be two `n`-element sets of residues mod `p`, and consider the
  integer polynomial `P(X) = det ((1 + X)^{a i * b j})`.
* Expanding `(1 + X)^{a i b j} = (1 + s_i)^{b_j}` with `s_i = (1+X)^{a i} - 1` and using
  multilinearity of the determinant in the rows, `P` is a sum over functions
  `f : Fin n → Fin p` of `(∏ i, s_i ^ f i) * det (choose (b j) (f i))`.
* The terms with non-injective `f` vanish, and the remaining ones are divisible by
  `X ^ (∑ i, f i)` with `∑ i, f i ≥ N := 0 + 1 + ⋯ + (n-1)`. Hence `X^N ∣ P`, and the
  coefficient of `X^N` is `det (vandermonde a) * det (choose (b i) j)`, which is **prime to `p`**
  (a Vandermonde determinant of distinct residues, divided by a superfactorial).
* If some `ζ^{a i b j}` determinant vanished, the shifted cyclotomic polynomial
  `Φ_p(X + 1)` would divide `P`.  Its coefficients are `p ∣ C(p, k+1)` for `k < p - 1` and
  `1` in degree `p - 1`; combined with `X^N ∣ P` this forces `p ∣ P.coeff N`, a contradiction.
-/

namespace ChebotarevDFT

open Polynomial Matrix Finset

/-! ## Combinatorial preliminaries -/


/-- The staircase number `N = 0 + 1 + ⋯ + (n-1)`. -/
def stair (n : ℕ) : ℕ := ∑ i ∈ Finset.range n, i



/-! ## Polynomial preliminaries -/




/-! ## The auxiliary polynomial -/

variable {n p : ℕ}

/-- The integral polynomial `P(X) = det ((1+X)^{a i * b j})`. -/
noncomputable def chebPoly (a b : Fin n → ℕ) : ℤ[X] :=
  (Matrix.of fun i j : Fin n => (1 + X : ℤ[X]) ^ (a i * b j)).det

/-- The determinant of the matrix of binomial coefficients `C(b i, j)`. -/
noncomputable def chooseDet (b : Fin n → ℕ) : ℤ :=
  (Matrix.of fun i j : Fin n => ((b i).choose (j : ℕ) : ℤ)).det




/-! ## The lowest coefficient -/





/-! ## The coefficient is prime to `p` -/




/-! ## The shifted cyclotomic polynomial -/

/-- `Φ_p(X + 1)`. -/
noncomputable def shiftedCyclotomic (p : ℕ) : ℤ[X] := (cyclotomic p ℤ).comp (X + 1)




/-! ## Main theorem -/





end ChebotarevDFT


