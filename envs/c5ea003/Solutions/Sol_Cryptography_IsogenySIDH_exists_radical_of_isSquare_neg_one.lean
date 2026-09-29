-- Prove2me | solution 1 for Cryptography.IsogenySIDH.exists_radical_of_isSquare_neg_one
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T18:20:06.211994+00:00
-- url     : https://prove2.me/submissions/4c8db7fb-8356-400f-bd0e-4211648a7db5

-- Sol generated from Cryptography/IsogenySIDH/SupersingularRadicalExistence.lean
import Mathlib
import Definitions.Def_Cryptography_IsogenySIDH_ModularTwoIsogeny
import Definitions.Def_Cryptography_IsogenySIDH_SupersingularRadicalExistence
/-
# Radicals always exist over quadratic finite fields

Radical isogeny algorithms are run on supersingular curves over `𝔽_{p²}`.  A
radical 2-isogeny step from the Montgomery parameter `A` needs a square root of
`A + 2`; if that root is missing one has to change the Montgomery model, using
instead `√(2-A)` or `√(A²-4)` (see `ModularTwoIsogeny`, where all three models
were shown to hit the same point of the `j`-line).

The main theorem of this file, `exists_radical_of_isSquare_neg_one`, is that at
least one of these three radicals is *always* available, as soon as `-1` is a
square in the base field.  The proof is a quadratic-character computation
resting on the identity

`(A+2)·(2-A) = -(A²-4)`,

so the three radicands multiply to minus a square: their quadratic characters
cannot all be `-1`.

`isSquare_neg_one_of_card_sq` specialises this to a field of square
cardinality — exactly the quadratic finite fields `𝔽_{p²}` of supersingular
isogeny cryptography — where `-1` is automatically a square.  Combined with the
model-independence theorem of `ModularTwoIsogeny` this yields
`exists_montgomery_quotient_model`: over `𝔽_{p²}` the 2-isogenous curve always
has a Montgomery model defined over the same field, so a radical walk never
needs a field extension.

The final section records small, fully checked supersingular instances of the
radical step, verified by `decide`.
-/

open Cryptography.IsogenySIDH

open Finset

/-! ## Existence of one of the three radicals -/


variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [Fintype F] [DecidableEq F] in
/-- The three radicands of the three Montgomery models of the quotient multiply
to minus a square. -/
theorem radicand_product (A : F) : (A + 2) * (2 - A) = -(A ^ 2 - 4) := by ring






/-! ## Verified supersingular instances

For a prime `p ≡ 3 mod 4` the curve `y² = x³ + x` over `𝔽_p` is supersingular,
so it has exactly `p + 1` points.  We check this and the corresponding radical
step by exhaustive computation. -/


instance : Fact (Nat.Prime 23) := ⟨by norm_num⟩















open Cryptography.IsogenySIDH in
theorem solution(hneg : IsSquare (-1 : F)) (A : F) :
    IsSquare (A + 2) ∨ IsSquare (2 - A) ∨ IsSquare (A ^ 2 - 4) := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨h1, h2, h3⟩ := hcon
  have hchi1 : quadraticChar F (A + 2) = -1 := quadraticChar_neg_one_iff_not_isSquare.mpr h1
  have hchi2 : quadraticChar F (2 - A) = -1 := quadraticChar_neg_one_iff_not_isSquare.mpr h2
  have hchi3 : quadraticChar F (A ^ 2 - 4) = -1 := quadraticChar_neg_one_iff_not_isSquare.mpr h3
  have hchineg : quadraticChar F (-1) = 1 :=
    (quadraticChar_one_iff_isSquare (a := (-1 : F)) (neg_ne_zero.mpr one_ne_zero)).mpr hneg
  have hprod : quadraticChar F ((A + 2) * (2 - A)) = 1 := by
    rw [map_mul, hchi1, hchi2]; norm_num
  rw [radicand_product] at hprod
  have hsplit : quadraticChar F (-(A ^ 2 - 4)) = -1 := by
    have hrw : (-(A ^ 2 - 4)) = (-1 : F) * (A ^ 2 - 4) := by ring
    rw [hrw, map_mul, hchineg, hchi3]; norm_num
  rw [hsplit] at hprod
  norm_num at hprod
