-- Prove2me | solution 1 for A4ForkPinning.no_rat_root_cubic
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T11:26:05.133985+00:00
-- url     : https://prove2.me/submissions/8d7e66de-638a-4d58-8108-896207f47b3d

-- Sol generated from Algebra/A4ForkPinning/Resolvent.lean
import Mathlib
import Definitions.Def_Algebra_A4ForkPinning_Resolvent
/-
# The Klein resolvent of `x⁴ + 8x + 12` and the conductor-9 cyclic cubic

The A₄-field of the experiment is the splitting field `L` of `x⁴ + 8x + 12`; the
fixed field `K = L^{V₄}` of the Klein group is the cubic field cut out by the
**Klein resolvent** `y³ - 48y - 64`, whose roots are `r₁r₂+r₃r₄`, `r₁r₃+r₂r₄`,
`r₁r₄+r₂r₃`.  This file proves, over an arbitrary commutative ring / field:

* `A4ForkPinning.klein_resolvent_root` — each `rᵢrⱼ + rₖrₗ` is a root of
  `y³ - 48y - 64` (Vieta computation, no analysis involved);
* `A4ForkPinning.klein_disc`, `A4ForkPinning.quartic_disc_eq_klein_disc`,
  `A4ForkPinning.quartic_disc` — the discriminant of the quartic equals that of
  its resolvent and equals `576²`: a **perfect square**, whence `Gal ⊆ A₄`;
* `A4ForkPinning.klein_resolvent_scaling` — `y³ - 48y - 64 = 64·(z³ - 3z - 1)`
  for `y = 4z`: the resolvent *is* the standard conductor-`9` cyclic cubic;
* `A4ForkPinning.zeta9_root` — `ζ₉ + ζ₉⁻¹` is a root of `z³ - 3z + 1`, and
  `A4ForkPinning.neg_zeta9_root` — `-(ζ₉+ζ₉⁻¹)` is a root of `z³ - 3z - 1`.
  So `K = ℚ(ζ₉)⁺`, the real cyclotomic field of **conductor 9**;
* `A4ForkPinning.no_rat_root_cubic`, `A4ForkPinning.klein_resolvent_no_rat_root`
  — the cubic is irreducible over `ℚ` (no rational root, degree 3), so `K` is a
  genuine cubic field;
* `A4ForkPinning.cubes_mod_nine` — the cubic residues mod `9` are exactly
  `{1, 8}`, a subgroup of index `3` in `(ℤ/9)ˣ`, and `A4ForkPinning.chi9` is the
  resulting cubic residue character with `chi9_mul`, `chi9_eq_zero_iff`.

Together: the `V₄`-fork of the A₄-field is governed by the cubic character mod `9`.
-/

open A4ForkPinning

open Finset

/-! ## Vieta for the Klein resolvent -/

variable {R : Type*} [CommRing R]





variable {a b c d : R}
  (h1 : a + b + c + d = 0)
  (h2 : a * b + a * c + a * d + b * c + b * d + c * d = 0)
  (h3 : a * b * c + a * b * d + a * c * d + b * c * d = -8)
  (h4 : a * b * c * d = 12)

include h1 h2 h3 h4






/-! ## Discriminants -/





variable {a b c d : R}
  (h1 : a + b + c + d = 0)
  (h2 : a * b + a * c + a * d + b * c + b * d + c * d = 0)
  (h3 : a * b * c + a * b * d + a * c * d + b * c * d = -8)
  (h4 : a * b * c * d = 12)

include h1 h2 h3 h4




/-! ## The resolvent *is* the conductor-9 cyclic cubic -/





/-! ## Irreducibility over `ℚ` -/



/-! ## The cubic residue character mod 9 -/








open A4ForkPinning in
theorem solution: ∀ z : ℚ, z ^ 3 - 3 * z + 1 ≠ 0 := by
  intro z hz
  have hden : (z.den : ℚ) ≠ 0 := by exact_mod_cast z.den_nz
  have hzz : (z.num : ℚ) = z * z.den := (div_eq_iff hden).1 (Rat.num_div_den z)
  have key : z.num ^ 3 - 3 * z.num * (z.den : ℤ) ^ 2 + (z.den : ℤ) ^ 3 = 0 := by
    have h : ((z.num : ℚ) ^ 3 - 3 * (z.num : ℚ) * ((z.den : ℤ) : ℚ) ^ 2
        + ((z.den : ℤ) : ℚ) ^ 3 : ℚ) = 0 := by
      push_cast
      rw [hzz]
      linear_combination ((z.den : ℚ)) ^ 3 * hz
    exact_mod_cast h
  have hb : (z.den : ℤ) ∣ z.num ^ 3 :=
    ⟨3 * z.num * (z.den : ℤ) - (z.den : ℤ) ^ 2, by linarith [key]⟩
  have hcop : IsCoprime z.num ((z.den : ℤ)) := by
    rw [Int.isCoprime_iff_gcd_eq_one]; exact z.reduced
  have hbu : IsUnit ((z.den : ℤ)) := (IsCoprime.pow_left hcop).isUnit_of_dvd' hb (dvd_refl _)
  have hb1 : (z.den : ℤ) = 1 := by
    rcases Int.isUnit_iff.1 hbu with h | h
    · exact h
    · exfalso
      have : (0 : ℤ) < z.den := by exact_mod_cast z.pos
      omega
  rw [hb1] at key
  have hdvd : z.num ∣ 1 := ⟨-(z.num ^ 2 - 3), by linarith [key]⟩
  rcases Int.isUnit_iff.1 (isUnit_of_dvd_one hdvd) with h | h <;> rw [h] at key <;> norm_num at key
