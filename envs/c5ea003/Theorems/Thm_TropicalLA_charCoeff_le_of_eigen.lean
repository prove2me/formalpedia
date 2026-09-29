-- Prove2me | Theorems.Thm_TropicalLA_charCoeff_le_of_eigen
-- name    : TropicalLA.charCoeff_le_of_eigen
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-17T19:17:37.271156+00:00
-- url     : https://prove2.me/theorems/161ea71a-0145-44fe-9bce-2773dbf0b6fe
-- title:
--   Upper bound on the characteristic coefficients: an eigenvalue `lam` forces
-- statement:
--   **Upper bound on the characteristic coefficients**: an eigenvalue `lam` forces
--   `c_k ≤ k · lam`.  (Each cell of the minor loses `lam` plus a telescoping eigenvector
--   difference, and the differences cancel because `σ` permutes `s`.)
--
--   ```lean
--   theorem TropicalLA.charCoeff_le_of_eigen(h : IsTropEigen A lam v) {k : ℕ} (hk : k ≤ Fintype.card ι) :
--       charCoeff A k ≤ k * lam := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/TropicalLinearAlgebra/TropicalCharPoly.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/TropicalLinearAlgebra/TropicalCharPoly.lean#L115

-- Thm stub generated from Algebra/TropicalLinearAlgebra/TropicalCharPoly.lean
import Mathlib
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalCharPoly
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalEigenvalue
/-
# The tropical characteristic polynomial and its roots

For a max-plus matrix `A` on an `n`-element index set the tropical characteristic
polynomial is

  `p_A(x) = max_{0 ≤ k ≤ n} ( c_k + (n - k)·x )`,   `c_k = max_{|s| = k, σ(s) = s} Σ_{i ∈ s} A i (σ i)`,

the coefficient `c_k` being the tropical determinant of the best principal `k × k`
minor (`charCoeff`).  A point `x` is a **tropical root** when the maximum defining
`p_A(x)` is attained at two different degrees `k` (the standard corner-locus
definition of a root of a tropical polynomial).

Main results:

* `charCoeff_card_eq_tdet` : the top coefficient is the tropical determinant;
* `charCoeff_le_of_eigen`  : if `lam` is an eigenvalue then `c_k ≤ k·lam` for all `k`;
* `exists_charCoeff_eq_of_eigen` : equality `c_k = k·lam` holds for some `1 ≤ k ≤ n`,
  witnessed by the critical cycle turned into a genuine permutation;
* `eigen_isTropicalRoot` : **every tropical eigenvalue is a root of the tropical
  characteristic polynomial**, with the maximum attained both at degree `0` and at
  the length of a critical cycle, and `p_A(lam) = n·lam`.
-/

open TropicalLA

variable {ι : Type*} [Fintype ι] [DecidableEq ι]











variable [Nonempty ι] {A : Matrix ι ι ℝ} {lam : ℝ} {v : ι → ℝ}

theorem TropicalLA.charCoeff_le_of_eigen(h : IsTropEigen A lam v) {k : ℕ} (hk : k ≤ Fintype.card ι) :
    charCoeff A k ≤ k * lam := by sorry
