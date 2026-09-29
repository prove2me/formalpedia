-- Prove2me | solution 1 for Cryptography.IsogenySIDH.isSquare_neg_one_of_card_sq
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T18:23:13.296966+00:00
-- url     : https://prove2.me/submissions/3175081c-b1cb-4b2e-bcfa-baee54b6e12d

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







/-! ## Verified supersingular instances

For a prime `p ≡ 3 mod 4` the curve `y² = x³ + x` over `𝔽_p` is supersingular,
so it has exactly `p + 1` points.  We check this and the corresponding radical
step by exhaustive computation. -/


instance : Fact (Nat.Prime 23) := ⟨by norm_num⟩















open Cryptography.IsogenySIDH in
omit [DecidableEq F] in
theorem solution(hF : ringChar F ≠ 2) {q : ℕ}
    (hcard : Fintype.card F = q ^ 2) : IsSquare (-1 : F) := by
  have hcardodd : Fintype.card F % 2 = 1 := FiniteField.odd_card_of_char_ne_two hF
  rw [hcard] at hcardodd
  have hqodd : q % 2 = 1 := by
    rcases Nat.even_or_odd q with he | ho
    · obtain ⟨k, hk⟩ := he
      subst hk
      have hsq : (k + k) ^ 2 = 2 * (2 * k ^ 2) := by ring
      rw [hsq] at hcardodd
      omega
    · obtain ⟨m, hm⟩ := ho
      omega
  have hmod : q ^ 2 % 4 = 1 := by
    obtain ⟨m, hm⟩ : Odd q := Nat.odd_iff.mpr hqodd
    subst hm
    have hsq : (2 * m + 1) ^ 2 = 4 * (m ^ 2 + m) + 1 := by ring
    rw [hsq]
    omega
  rw [FiniteField.isSquare_neg_one_iff, hcard, hmod]
  norm_num
