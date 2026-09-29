-- Prove2me | Theorems.Thm_ChebotarevDFT_prime_dvd_coeff_of_shiftedCyclotomic_dvd
-- name    : ChebotarevDFT.prime_dvd_coeff_of_shiftedCyclotomic_dvd
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:21:42.247073+00:00
-- url     : https://prove2.me/theorems/df27e8af-4ce2-408d-aeae-1b839828244e
-- title:
--   Frenkel's divisibility step: if the shifted cyclotomic polynomial divides `P` and `P`
-- statement:
--   Frenkel's divisibility step: if the shifted cyclotomic polynomial divides `P` and `P`
--   vanishes to order `N` at `0`, then `p` divides the `N`-th coefficient of `P`.
--
--   ```lean
--   theorem ChebotarevDFT.prime_dvd_coeff_of_shiftedCyclotomic_dvd(hp : p.Prime) (P : ℤ[X]) (N : ℕ)
--       (hdvd : shiftedCyclotomic p ∣ P) (hlow : ∀ m < N, P.coeff m = 0) :
--       (p : ℤ) ∣ P.coeff N := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/ChebotarevDFT.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/ChebotarevDFT.lean#L355

-- Thm stub generated from Novelty/ChebotarevDFT.lean
import Mathlib
import Definitions.Def_Novelty_ChebotarevDFT
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

open ChebotarevDFT

open Polynomial Matrix Finset

/-! ## Combinatorial preliminaries -/





/-! ## Polynomial preliminaries -/




/-! ## The auxiliary polynomial -/

variable {n p : ℕ}






/-! ## The lowest coefficient -/





/-! ## The coefficient is prime to `p` -/




/-! ## The shifted cyclotomic polynomial -/

theorem ChebotarevDFT.prime_dvd_coeff_of_shiftedCyclotomic_dvd(hp : p.Prime) (P : ℤ[X]) (N : ℕ)
    (hdvd : shiftedCyclotomic p ∣ P) (hlow : ∀ m < N, P.coeff m = 0) :
    (p : ℤ) ∣ P.coeff N := by sorry
