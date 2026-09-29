-- Prove2me | solution 1 for Cryptography.IsogenySIDH.exists_montgomery_quotient_model
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T18:23:12.326833+00:00
-- url     : https://prove2.me/submissions/5c01af01-a613-40e8-9e5f-829c2c5caa3a

-- Sol generated from Cryptography/IsogenySIDH/SupersingularRadicalExistence.lean
import Mathlib
import Definitions.Def_Cryptography_IsogenySIDH_ModularTwoIsogeny
import Definitions.Def_Cryptography_IsogenySIDH_RadicalMontgomeryFormula
import Definitions.Def_Cryptography_IsogenySIDH_SupersingularRadicalExistence
import Theorems.Thm_Cryptography_IsogenySIDH_exists_radical_of_isSquare_neg_one
import Theorems.Thm_Cryptography_IsogenySIDH_jMont_radTwoParam
import Theorems.Thm_Cryptography_IsogenySIDH_jMont_radTwoParamCentre
import Theorems.Thm_Cryptography_IsogenySIDH_jMont_radTwoParamMinus
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
theorem solution(hF : ringChar F ≠ 2)
    (hneg : IsSquare (-1 : F)) {A : F} (hd : A ^ 2 - 4 ≠ 0) :
    ∃ A' : F, jMont A' = jQuot A := by
  have htwo : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  have hAp2 : A + 2 ≠ 0 := fun h => hd (by linear_combination (A - 2) * h)
  have hAm2 : A - 2 ≠ 0 := fun h => hd (by linear_combination (A + 2) * h)
  rcases exists_radical_of_isSquare_neg_one hneg A with hs | hs | hs
  · obtain ⟨a, ha⟩ := hs
    have hsq : a ^ 2 = A + 2 := by rw [ha]; ring
    have ha0 : a ≠ 0 := by
      intro h; apply hAp2; rw [← hsq, h]; ring
    exact ⟨radTwoParam A a, jMont_radTwoParam htwo ha0 hsq hd⟩
  · obtain ⟨g, hg⟩ := hs
    have hsq : g ^ 2 = 2 - A := by rw [hg]; ring
    have hg0 : g ≠ 0 := by
      intro h
      apply hAm2
      have : (2 : F) - A = 0 := by rw [← hsq, h]; ring
      linear_combination -this
    exact ⟨radTwoParamMinus A g, jMont_radTwoParamMinus htwo hg0 hsq hd⟩
  · obtain ⟨d, hdd⟩ := hs
    have hsq : d ^ 2 = A ^ 2 - 4 := by rw [hdd]; ring
    have hd0 : d ≠ 0 := by
      intro h; apply hd; rw [← hsq, h]; ring
    exact ⟨radTwoParamCentre A d, jMont_radTwoParamCentre htwo hd0 hsq⟩
