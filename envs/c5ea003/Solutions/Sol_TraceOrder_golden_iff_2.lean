-- Prove2me | solution 2 for TraceOrder.golden_iff
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T16:42:03.558264+00:00
-- url     : https://prove2.me/submissions/3b95cfe7-0b18-4937-a181-022fdaa700d8

import Mathlib
import Definitions.Def_Applications_CyclicCubicTypeChannel_Splitting
import Definitions.Def_Applications_CyclicCubicTypeChannel_TraceOrder
open Matrix TraceOrder in
theorem solution (p : ℕ) [hp : Fact p.Prime] (hp5 : p ≠ 5) :
    (∃ x : ZMod p, x ^ 2 + x - 1 = 0) ↔ ((p : ZMod 5) = 1 ∨ (p : ZMod 5) = 4) := by
  -- the nonzero squares mod `5` are `1` and `4`
  have hsq5 : ∀ y : ZMod 5, y ≠ 0 → (IsSquare y ↔ y = 1 ∨ y = 4) := by decide
  have hF2 : ∀ y : ZMod 2, y ^ 2 + y - 1 ≠ 0 := by decide
  by_cases hp2 : p = 2
  · -- over `𝔽₂` the polynomial `x² + x + 1` has no root, and `2 ≢ ±1 (mod 5)`
    subst hp2
    constructor
    · rintro ⟨x, hx⟩
      exact absurd hx (hF2 x)
    · intro h
      exfalso
      revert h
      decide
  · haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    have h2 : (2 : ZMod p) ≠ 0 := by
      intro h
      have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
      rw [ZMod.natCast_eq_zero_iff] at h'
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp h')
    have hp0 : (p : ZMod 5) ≠ 0 := by
      intro h
      rw [ZMod.natCast_eq_zero_iff] at h
      exact hp5 ((Nat.prime_dvd_prime_iff_eq (by norm_num) hp.out).mp h).symm
    -- a root exists iff the discriminant `5` is a square mod `p`: `(2x+1)² = 4(x²+x-1) + 5`
    have hroot : (∃ x : ZMod p, x ^ 2 + x - 1 = 0) ↔ IsSquare (5 : ZMod p) := by
      constructor
      · rintro ⟨x, hx⟩
        exact ⟨2 * x + 1, by linear_combination (-4 : ZMod p) * hx⟩
      · rintro ⟨s, hs⟩
        refine ⟨(s - 1) / 2, ?_⟩
        field_simp
        linear_combination (-1 : ZMod p) * hs
    -- quadratic reciprocity with `5 ≡ 1 (mod 4)`
    have hQR := ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one (p := 5) (q := p) (by norm_num) hp2
    push_cast at hQR
    rw [hroot, ← hQR, hsq5 _ hp0]
