-- Prove2me | Definitions.Def_Cryptography_BerggrenModular_Threshold
-- name    : Cryptography_BerggrenModular_Threshold
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T02:07:08.848363+00:00
-- url     : https://prove2.me/theorems/dd27eeea-8106-48d5-854b-70942380f69b
-- title:
--   Aether Catalog definitions — Cryptography_BerggrenModular_Threshold
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.BerggrenModular.Threshold`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/BerggrenModular/Threshold.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Cryptography_BerggrenModular_Core
import Definitions.Def_Cryptography_BerggrenModular_Hardness
import Definitions.Def_Cryptography_BerggrenModular_Modular

/-!
# The modulus threshold: where seed recovery flips from easy to impossible

`Cryptography.BerggrenModular.Hardness` shows that modular seed recovery is
impossible once `m³ < 3^k`.  This file proves the **positive companion**: if the
modulus is large enough that no state of a length-`k` trajectory can wrap around,
then a modular observer recovers the control word exactly, by the same
`whichMove` peeling used over `ℤ`.

The growth bound is `c ↦ ≤ 7c` per move, so a length-`k` trajectory from the root
`(3,4,5)` stays below `5·7^k`.  Hence

* `modSeedRecoverable_of_large_modulus` : `5·7^k < m` ⟹ recovery is possible;
* `not_modSeedRecoverable_of_card`      : `m³ < 3^k` ⟹ recovery is impossible.

Writing `m = 7^{αk}` the transition therefore sits somewhere in
`α ∈ [log 3 / (3 log 7), 1]`, and pinning it down is left as an explicit open
problem in `FUTURE_DIRECTIONS.md`.

## Main results

* `hyp_applyWord_le` — the `7^k` growth bound along any control word.
* `liftTri_stateMod` — below the threshold the modular observation determines the
  integer state.
* `recoverModFrom_correct`, `modSeedRecoverable_of_large_modulus`.
* `berggren_threshold_sandwich` — the two-sided statement.
-/

namespace Cryptography
namespace BerggrenModular

/-! ## Growth of the hypotenuse -/




/-! ## Below the threshold the residue determines the state -/



/-! ## Self-terminating modular recovery -/

/-- Modular seed recovery with a root test: peel moves off the observed residue
until the residue of the root is reached. -/
def recoverModFrom (m : ℕ) [NeZero m] : ℕ → TriM m → List Move
  | 0, _ => []
  | n + 1, w =>
      if w = redTri m root then []
      else whichMoveMod m w :: recoverModFrom m n (invMoveM m (whichMoveMod m w) w)



/-! ## The sandwich -/



end BerggrenModular
end Cryptography


