-- Prove2me | Theorems.Thm_ThreeCubes_hasse_of_abs_le_113
-- name    : ThreeCubes.hasse_of_abs_le_113
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:13:24.419364+00:00
-- url     : https://prove2.me/theorems/34f2d8e9-b579-4818-85a5-e01716075347
-- title:
--   The Hasse principle holds for every `|n| ≤ 113`.
-- statement:
--   **The Hasse principle holds for every `|n| ≤ 113`.**  Since `114` is the smallest locally
--   solvable positive integer with no known representation, this is the largest symmetric window
--   that can currently be certified.
--
--   ```lean
--   theorem ThreeCubes.hasse_of_abs_le_113(n : ℤ) (h : |n| ≤ 113) : HasseHolds n := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/Witnesses.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/Witnesses.lean#L154

-- Thm stub generated from Probability/Witnesses.lean
import Mathlib
import Definitions.Def_Probability_Witnesses

/-!
# Verified computational results and the Hasse principle for `x³ + y³ + z³ = n`

The theorem `ThreeCubes.locallySolvable_iff` shows that the only local obstruction is the
congruence mod `9`.  Whether every locally solvable `n` is *globally* solvable — the Hasse
principle for the affine surface — is a famous open problem.  Here we

* reformulate the conjecture purely in congruence terms (`hasse_iff_congruence`);
* **verify it for every `n` with `|n| ≤ 113`**, using explicit representations checked by the
  Lean kernel.  This is the widest window currently possible: `114` is the smallest positive
  integer that is locally solvable and for which no representation is known.  Several of the
  witnesses are genuinely large, the most famous being
  `33 = 8866128975287528³ - 8778405442862239³ - 2736111468807040³` and
  `42 = (-80538738812075974)³ + 80435758145817515³ + 12602123297335631³`;
* record a second, huge representation of `3`.
-/

open ThreeCubes

theorem ThreeCubes.hasse_of_abs_le_113(n : ℤ) (h : |n| ≤ 113) : HasseHolds n := by sorry
