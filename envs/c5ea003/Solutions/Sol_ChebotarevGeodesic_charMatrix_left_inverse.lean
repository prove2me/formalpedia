-- Prove2me | solution 1 for ChebotarevGeodesic.charMatrix_left_inverse
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T20:42:20.80293+00:00
-- url     : https://prove2.me/submissions/32a4e42f-49bc-415d-bfde-501c7ecdb5a6

-- Sol generated from Shared/ChebotarevGeodesicCharacter.lean
import Mathlib
import Definitions.Def_Shared_ChebotarevGeodesic
import Definitions.Def_Shared_ChebotarevGeodesicCharacter
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

open ChebotarevGeodesic

/-! ## The complex-valued exponent calculus -/


variable {pi pi₁ pi₂ M M₁ M₂ : ℝ → ℂ} {θ : ℝ}







/-! ## The transfer principle over `ℂ` -/


/-! ## The character table of a finite abelian group is invertible -/


variable (α : Type*) [AddCommGroup α] [Fintype α] [DecidableEq α]








open ChebotarevGeodesic in
theorem solution: charMatrixInv α * charMatrix α = 1 := by
  have hcard : (Fintype.card α : ℂ) ≠ 0 := by
    have hpos : 0 < Fintype.card α := Fintype.card_pos
    exact_mod_cast Nat.cast_ne_zero.mpr hpos.ne'
  ext a b
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hterm : ∀ psi : AddChar α ℂ,
      charMatrixInv α a psi * charMatrix α psi b
        = (Fintype.card α : ℂ)⁻¹ * psi (-a + b) := by
    intro psi
    rw [charMatrixInv, charMatrix, psi.map_add_eq_mul]
    ring
  rw [Finset.sum_congr rfl fun psi _ => hterm psi, ← Finset.mul_sum,
    AddChar.sum_apply_eq_ite (-a + b)]
  by_cases hab : a = b
  · subst hab
    simp [hcard]
  · have hne : -a + b ≠ 0 := by
      intro hzero
      exact hab (by linear_combination (norm := abel) -hzero)
    simp [hne, hab]
