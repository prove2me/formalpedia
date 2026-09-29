-- Prove2me | Theorems.Thm_TropicalLA_MaxPlus_toBot_matrix_mul
-- name    : TropicalLA.MaxPlus.toBot_matrix_mul
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:59:31.05412+00:00
-- url     : https://prove2.me/theorems/a064ee3e-fa7c-4679-bf97-e0dd2b9271c8
-- title:
--   The entries of a tropical matrix product: `(A ⊗ B) i j = max_k (A i k + B k j)`,
-- statement:
--   The entries of a tropical matrix product: `(A ⊗ B) i j = max_k (A i k + B k j)`,
--   where `max` and `+` are taken in `R ∪ {-∞}`.
--
--   ```lean
--   theorem TropicalLA.MaxPlus.toBot_matrix_mul(A B : Matrix ι ι (MaxPlus R)) (i j : ι) :
--       toBot ((A * B) i j) = Finset.univ.sup (fun k => toBot (A i k) + toBot (B k j)) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/TropicalLinearAlgebra/MaxPlusSemiring.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/TropicalLinearAlgebra/MaxPlusSemiring.lean#L119

-- Thm stub generated from Algebra/TropicalLinearAlgebra/MaxPlusSemiring.lean
import Mathlib
import Definitions.Def_Algebra_TropicalLinearAlgebra_MaxPlusSemiring
/-
# The max-plus (tropical) semiring

We construct the tropical semiring `(R ∪ {-∞}, max, +)` as a type synonym
`MaxPlus R := WithBot R` for a linearly ordered additive commutative monoid `R`
(the motivating case being `R = ℝ`), equip it with a `CommSemiring` structure,
and record its characteristic tropical features:

* it is **idempotent**: `a + a = a`;
* it is **zero-sum-free**: `a + b = 0 → a = 0 ∧ b = 0`, so (for nontrivial `R`)
  it admits no additive inverses and is genuinely not a ring;
* finite tropical sums are suprema (`toBot_sum`);
* consequently tropical matrix multiplication is the `max`-of-sums formula and
  is associative.
-/

open TropicalLA


open MaxPlus





/-- Tropical multiplication is ordinary addition. -/
instance {R : Type*} [Add R] : Mul (MaxPlus R) := ⟨fun a b => ofBot (toBot a + toBot b)⟩


variable {R : Type*} [AddCommMonoid R] [LinearOrder R] [IsOrderedAddMonoid R]









variable {ι : Type*} [Fintype ι]

theorem TropicalLA.MaxPlus.toBot_matrix_mul(A B : Matrix ι ι (MaxPlus R)) (i j : ι) :
    toBot ((A * B) i j) = Finset.univ.sup (fun k => toBot (A i k) + toBot (B k j)) := by sorry
