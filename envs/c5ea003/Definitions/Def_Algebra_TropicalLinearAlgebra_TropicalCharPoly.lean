-- Prove2me | Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalCharPoly
-- name    : Algebra_TropicalLinearAlgebra_TropicalCharPoly
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-17T16:29:09.766539+00:00
-- url     : https://prove2.me/theorems/0cb702fb-d692-43d0-a64c-f38654ea8fbf
-- title:
--   Aether Catalog definitions — Algebra_TropicalLinearAlgebra_TropicalCharPoly
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.TropicalLinearAlgebra.TropicalCharPoly`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/TropicalLinearAlgebra/TropicalCharPoly.lean by skeleton subtraction
import Mathlib
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

namespace TropicalLA

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The weight of the permutation `σ` restricted to the principal minor on `s`. -/
def minorWeight (A : Matrix ι ι ℝ) (s : Finset ι) (σ : Equiv.Perm ι) : ℝ := ∑ i ∈ s, A i (σ i)

/-- Pairs `(s, σ)` with `|s| = k` and `σ` mapping `s` to itself: these index the
principal `k × k` minors together with a permutation of the minor. -/
noncomputable def admPairs (ι : Type*) [Fintype ι] [DecidableEq ι] (k : ℕ) :
    Finset (Finset ι × Equiv.Perm ι) :=
  Finset.univ.filter (fun p => p.1.card = k ∧ ∀ i ∈ p.1, p.2 i ∈ p.1)



/-- The `k`-th coefficient of the tropical characteristic polynomial: the tropical
determinant of the best principal `k × k` minor. -/
noncomputable def charCoeff (A : Matrix ι ι ℝ) (k : ℕ) : ℝ :=
  if h : (admPairs ι k).Nonempty then (admPairs ι k).sup' h (fun p => minorWeight A p.1 p.2)
  else 0





section Eigen

variable [Nonempty ι] {A : Matrix ι ι ℝ} {lam : ℝ} {v : ι → ℝ}





end Eigen

/-- Value of the tropical characteristic polynomial `p_A(x)`. -/
noncomputable def charPolyVal (A : Matrix ι ι ℝ) (x : ℝ) : ℝ :=
  (Finset.range (Fintype.card ι + 1)).sup' (by simp)
    (fun k => charCoeff A k + ((Fintype.card ι : ℝ) - k) * x)

/-- `x` is a **tropical root** of the characteristic polynomial of `A` if the maximum
defining `p_A(x)` is attained at two different degrees. -/
def IsTropicalRoot (A : Matrix ι ι ℝ) (x : ℝ) : Prop :=
  ∃ k₁ k₂ : ℕ, k₁ ≤ Fintype.card ι ∧ k₂ ≤ Fintype.card ι ∧ k₁ ≠ k₂ ∧
    charCoeff A k₁ + ((Fintype.card ι : ℝ) - k₁) * x = charPolyVal A x ∧
    charCoeff A k₂ + ((Fintype.card ι : ℝ) - k₂) * x = charPolyVal A x


end TropicalLA


