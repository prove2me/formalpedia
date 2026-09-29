-- Prove2me | Definitions.Def_Algebra_A4ForkPinning_Resolvent
-- name    : Algebra_A4ForkPinning_Resolvent
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T08:02:37.683878+00:00
-- url     : https://prove2.me/theorems/ca781ec9-8ef2-46b0-b067-47d41e6e4f61
-- title:
--   Aether Catalog definitions — Algebra_A4ForkPinning_Resolvent
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.A4ForkPinning.Resolvent`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/A4ForkPinning/Resolvent.lean by skeleton subtraction
import Mathlib
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

namespace A4ForkPinning

open Finset

/-! ## Vieta for the Klein resolvent -/

variable {R : Type*} [CommRing R]




section Quartic

variable {a b c d : R}
  (h1 : a + b + c + d = 0)
  (h2 : a * b + a * c + a * d + b * c + b * d + c * d = 0)
  (h3 : a * b * c + a * b * d + a * c * d + b * c * d = -8)
  (h4 : a * b * c * d = 12)

include h1 h2 h3 h4





end Quartic

/-! ## Discriminants -/




section Disc

variable {a b c d : R}
  (h1 : a + b + c + d = 0)
  (h2 : a * b + a * c + a * d + b * c + b * d + c * d = 0)
  (h3 : a * b * c + a * b * d + a * c * d + b * c * d = -8)
  (h4 : a * b * c * d = 12)

include h1 h2 h3 h4



end Disc

/-! ## The resolvent *is* the conductor-9 cyclic cubic -/





/-! ## Irreducibility over `ℚ` -/



/-! ## The cubic residue character mod 9 -/



/-- The cubic residue character mod `9`, valued in `ℤ/3`
(`{1,8} ↦ 0`, `{2,7} ↦ 1`, `{4,5} ↦ 2`). -/
def chi9 (x : ZMod 9) : ZMod 3 :=
  if x = 1 ∨ x = 8 then 0 else if x = 2 ∨ x = 7 then 1 else 2

/-- `chi9` is multiplicative on units: it is a genuine cubic Dirichlet character. -/
theorem chi9_mul : ∀ x y : ZMod 9, IsUnit x → IsUnit y → chi9 (x * y) = chi9 x + chi9 y := by
  decide



end A4ForkPinning


