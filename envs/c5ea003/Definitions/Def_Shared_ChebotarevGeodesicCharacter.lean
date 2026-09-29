-- Prove2me | Definitions.Def_Shared_ChebotarevGeodesicCharacter
-- name    : Shared_ChebotarevGeodesicCharacter
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T07:35:17.911649+00:00
-- url     : https://prove2.me/theorems/17b1d884-4e06-4571-8517-5d4a12ba01c5
-- title:
--   Aether Catalog definitions — Shared_ChebotarevGeodesicCharacter
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.ChebotarevGeodesicCharacter`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/ChebotarevGeodesicCharacter.lean by skeleton subtraction
import Mathlib
/-
# The character-table reduction of the non-split case (abelian covers)

Conjecture C5 of `FUTURE_DIRECTIONS.md`.  The informal sentence "the non-split case reduces to
the split (character-twisted) case, with no loss in the exponent" becomes a theorem as soon as
one knows that the character table is an *invertible* transfer matrix.  Over `ℝ` this was
already available in the abstract (`exponent_of_inverse_transform`,
`transfer_iff_det_ne_zero`); the missing ingredient was the invertibility itself, which lives
over `ℂ` and comes from the orthogonality relations.

This file supplies the complex-valued half of the theory:

* `HasErrorExponentC` : the `ℂ`-valued analogue of `HasErrorExponent`, with the same calculus
  (`add`, `const_mul`, `sum`, `linear_comb`);
* `hasErrorExponentC_ofReal_iff` : it restricts to the real-valued notion;
* `exponentC_of_inverse_transform` : the transfer principle for a (possibly rectangular)
  complex transform admitting a left inverse;
* `charMatrix_left_inverse` : **the character table of a finite abelian group is invertible**,
  with explicit left inverse `(a, ψ) ↦ ψ(-a)/|α|`, proved from the orthogonality relation
  `∑_ψ ψ(a) = |α|·[a = 0]`;
* `hasErrorExponentC_character_iff` : consequently the twisted counting functions
  `π_ψ = ∑_a ψ(a) π_a` satisfy the estimate with exponent `θ` **iff** every individual
  `π_a` does;
* `chebotarev_abelian_character_reduction` : the real-valued statement for an abelian cover —
  since in an abelian group each conjugacy class is a single element, this is exactly the
  equivalence "non-split Chebotarev estimate ⟺ finitely many split (character-twisted)
  estimates", with no loss in the exponent.
-/


open Finset Filter
open scoped Topology

namespace ChebotarevGeodesic

/-! ## The complex-valued exponent calculus -/

/-- The `ℂ`-valued analogue of `HasErrorExponent`. -/
def HasErrorExponentC (pi M : ℝ → ℂ) (θ : ℝ) : Prop :=
  ∀ ε > 0, ∃ C > 0, ∃ X ≥ (1 : ℝ), ∀ x ≥ X, ‖pi x - M x‖ ≤ C * x ^ (θ + ε)

variable {pi pi₁ pi₂ M M₁ M₂ : ℝ → ℂ} {θ : ℝ}







/-! ## The transfer principle over `ℂ` -/


/-! ## The character table of a finite abelian group is invertible -/

section Character

variable (α : Type*) [AddCommGroup α] [Fintype α] [DecidableEq α]

/-- The character table of a finite abelian group: rows indexed by characters, columns by
group elements. -/
def charMatrix : Matrix (AddChar α ℂ) α ℂ := fun psi a => psi a

/-- The explicit left inverse of the character table, given by the orthogonality relations. -/
noncomputable def charMatrixInv : Matrix α (AddChar α ℂ) ℂ :=
  fun a psi => (Fintype.card α : ℂ)⁻¹ * psi (-a)




end Character

end ChebotarevGeodesic


