-- Prove2me | Definitions.Def_Probability_Witnesses
-- name    : Probability_Witnesses
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:24:01.692885+00:00
-- url     : https://prove2.me/theorems/5005fbf9-3826-4f3b-84ad-8d27041274e8
-- title:
--   Aether Catalog definitions — Probability_Witnesses
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.Witnesses`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/Witnesses.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Probability_Basic

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

namespace ThreeCubes

/-- The Hasse principle for the affine surface `x³ + y³ + z³ = n`: local solvability implies
global solvability.  This is an open conjecture in general. -/
def HasseHolds (n : ℤ) : Prop := LocallySolvable n → IsSumOfThreeCubes n





end ThreeCubes


