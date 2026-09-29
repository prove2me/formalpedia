-- Prove2me | solution 1 for A4ForkPinning.zeta9_root
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T11:26:05.658571+00:00
-- url     : https://prove2.me/submissions/cc7539dc-ecd5-460d-8a4d-c9b36d9e31ba

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
theorem solution{K : Type*} [Field K] (zeta : K) (h9 : zeta ^ 9 = 1) (h3 : zeta ^ 3 ≠ 1) :
    (zeta + zeta⁻¹) ^ 3 - 3 * (zeta + zeta⁻¹) + 1 = 0 := by
  have hz : zeta ≠ 0 := by
    intro h
    rw [h] at h9
    simp at h9
  have hu : (zeta ^ 3) ^ 3 = 1 := by rw [← pow_mul]; simpa using h9
  have hfac : (zeta ^ 3 - 1) * ((zeta ^ 3) ^ 2 + zeta ^ 3 + 1) = 0 := by linear_combination hu
  have hsum : (zeta ^ 3) ^ 2 + zeta ^ 3 + 1 = 0 := by
    rcases mul_eq_zero.1 hfac with h | h
    · exact absurd (by linear_combination h : zeta ^ 3 = 1) h3
    · exact h
  field_simp
  linear_combination hsum
