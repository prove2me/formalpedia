-- Prove2me | Theorems.Thm_ThreeCubes_isSumOfThreeCubes_of_nonneg_le_113
-- name    : ThreeCubes.isSumOfThreeCubes_of_nonneg_le_113
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:13:20.425072+00:00
-- url     : https://prove2.me/theorems/e32b5dcc-b3d2-40f3-8dbd-8d07975b924c
-- title:
--   Explicit representations for every `0 ≤ n ≤ 113` with `n ≢ ±4 (mod 9)`.
-- statement:
--   Explicit representations for every `0 ≤ n ≤ 113` with `n ≢ ±4 (mod 9)`.
--
--   ```lean
--   theorem ThreeCubes.isSumOfThreeCubes_of_nonneg_le_113(n : ℤ) (h0 : 0 ≤ n) (h1 : n ≤ 113)
--       (h4 : n % 9 ≠ 4) (h5 : n % 9 ≠ 5) : IsSumOfThreeCubes n := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/Witnesses.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/Witnesses.lean#L36

-- Thm stub generated from Probability/Witnesses.lean
import Mathlib
import Definitions.Def_Probability_Basic
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

theorem ThreeCubes.isSumOfThreeCubes_of_nonneg_le_113(n : ℤ) (h0 : 0 ≤ n) (h1 : n ≤ 113)
    (h4 : n % 9 ≠ 4) (h5 : n % 9 ≠ 5) : IsSumOfThreeCubes n := by sorry
