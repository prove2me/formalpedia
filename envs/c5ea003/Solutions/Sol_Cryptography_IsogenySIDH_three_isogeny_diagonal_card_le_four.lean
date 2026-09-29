-- Prove2me | solution 1 for Cryptography.IsogenySIDH.three_isogeny_diagonal_card_le_four
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T04:54:05.529025+00:00
-- url     : https://prove2.me/submissions/38aa4f10-af16-449e-84c5-dd4b65d8854f

-- Sol generated from Cryptography/IsogenySIDH/ThreeIsogenyFixedPoints.lean
import Mathlib
import Definitions.Def_Cryptography_IsogenySIDH_ThreeIsogenyFixedPoints
import Definitions.Def_Cryptography_IsogenySIDH_ThreeIsogenyMontgomery
/-
# Fixed points of a 3-isogeny step on the `j`-line

`RadicalWalkStructure.lean` classified the `j`-invariants that a *2*-isogeny
step can fix, by factoring the diagonal of the level-2 modular polynomial:
`Φ₂(j,j) = -(j-8000)(j+3375)²(j-1728)`.  The level-3 side, developed in
`ThreeIsogenyMontgomery.lean`, supplied the explicit Costello–Hisil 3-isogeny
and the certificate `Φ₃(j(E_A), j(E_{A'})) = 0`, but left the corresponding
question open:

> can a 3-isogeny step of the Montgomery family return to the same
> `j`-invariant?

This file answers it completely.

* `modPoly3_diagonal_factor` — the diagonal of `Φ₃` factors as
  `Φ₃(j,j) = -j (j-8000)² (j-54000) (j+32768)²`,
  a polynomial identity of degree six.  The four roots are exactly the CM
  `j`-invariants of discriminants `-3`, `-8`, `-12` and `-11`, i.e. the
  `j`-invariants of the curves carrying an endomorphism of norm three.
* `three_isogeny_fixed_point_classification` — consequently a 3-isogeny step can
  fix a `j`-invariant only at `j ∈ {0, 8000, 54000, -32768}`.
* `modPoly3_diagonal_roots` — all four values really are zeroes of `Φ₃(j,j)`, so
  the list cannot be shortened on the level of the modular polynomial.
* `three_isogeny_step_moves` — the geometric consequence for the Montgomery
  family: away from those four values, the Costello–Hisil 3-isogeny genuinely
  changes the `j`-invariant.
* `three_isogeny_diagonal_card_le_four` — over any field at most four
  `j`-invariants can be fixed.

Together with `RadicalNonBacktracking.lean` and
`BacktrackingCharacteristic.lean` this completes the picture of *stationary*
behaviour for both levels handled in this thread: level 2 fixes at most the
three CM values `{1728, 8000, -3375}`, level 3 at most the four CM values
`{0, 8000, 54000, -32768}`, and the only value common to both lists is `8000`
(discriminant `-8`).
-/

set_option maxHeartbeats 1000000

open Cryptography.IsogenySIDH

open Polynomial

variable {K : Type*} [Field K]

/-! ## The diagonal of the level-three modular polynomial -/

/-- **Diagonal factorisation of `Φ₃`.**  The degree-six polynomial `Φ₃(j,j)`
factors completely over `ℚ`:
`Φ₃(j,j) = -j (j-8000)² (j-54000) (j+32768)²`.
Its roots are the CM `j`-invariants of discriminants `-3`, `-8`, `-12`, `-11`,
which are precisely the `j`-invariants admitting an endomorphism of norm
three. -/
theorem modPoly3_diagonal_factor (j : K) :
    modPoly3 j j = -(j * (j - 8000) ^ 2 * (j - 54000) * (j + 32768) ^ 2) := by
  simp only [modPoly3]; ring


/-! ## Classification of the fixed `j`-invariants -/

/-- **Classification of 3-isogeny fixed points.**  A zero of the diagonal of the
level-three modular polynomial is one of the four CM values `0`, `8000`,
`54000`, `-32768`. -/
theorem three_isogeny_fixed_point_classification {j : K} (h : modPoly3 j j = 0) :
    j = 0 ∨ j = 8000 ∨ j = 54000 ∨ j = -32768 := by
  rw [modPoly3_diagonal_factor, neg_eq_zero] at h
  rcases mul_eq_zero.mp h with h1 | h1
  · rcases mul_eq_zero.mp h1 with h2 | h2
    · rcases mul_eq_zero.mp h2 with h3 | h3
      · exact Or.inl h3
      · exact Or.inr (Or.inl (sub_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h3)))
    · exact Or.inr (Or.inr (Or.inl (sub_eq_zero.mp h2)))
  · have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h1
    exact Or.inr (Or.inr (Or.inr (by linear_combination this)))


/-! ## A counting bound for the diagonal -/






/-! ## Comparison of the two levels -/



open Cryptography.IsogenySIDH in
theorem solution[DecidableEq K] (S : Finset K) (hS : ∀ j ∈ S, modPoly3 j j = 0) : S.card ≤ 4 := by
  have hsub : S ⊆ ({0, 8000, 54000, -32768} : Finset K) := by
    intro j hj
    rcases three_isogeny_fixed_point_classification (hS j hj) with h | h | h | h <;> simp [h]
  have hc : ({0, 8000, 54000, -32768} : Finset K).card ≤ 4 := by
    have h1 : ({-32768} : Finset K).card = 1 := Finset.card_singleton _
    have h2 := Finset.card_insert_le (54000 : K) ({-32768} : Finset K)
    have h3 := Finset.card_insert_le (8000 : K) ({54000, -32768} : Finset K)
    have h4 := Finset.card_insert_le (0 : K) ({8000, 54000, -32768} : Finset K)
    simp only [Finset.insert_eq] at *
    omega
  exact (Finset.card_le_card hsub).trans hc
