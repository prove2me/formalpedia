-- Prove2me | Theorems.Thm_A4ForkPinning_card_units_mod_nine
-- name    : A4ForkPinning.card_units_mod_nine
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:24:01.381394+00:00
-- url     : https://prove2.me/theorems/d2cd521c-337c-40e1-a8f9-e13f75eaea8d
-- title:
--   Card units mod nine
-- statement:
--   Formal statement of `A4ForkPinning.card_units_mod_nine` from the Aether Catalog (Algebra). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem A4ForkPinning.card_units_mod_nine: Fintype.card (ZMod 9)ˣ = 6 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/A4ForkPinning/Resolvent.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/A4ForkPinning/Resolvent.lean#L234

-- Thm stub generated from Algebra/A4ForkPinning/Resolvent.lean
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

theorem A4ForkPinning.card_units_mod_nine: Fintype.card (ZMod 9)ˣ = 6 := by sorry
