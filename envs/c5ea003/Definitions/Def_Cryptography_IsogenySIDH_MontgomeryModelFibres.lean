-- Prove2me | Definitions.Def_Cryptography_IsogenySIDH_MontgomeryModelFibres
-- name    : Cryptography_IsogenySIDH_MontgomeryModelFibres
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T02:17:22.706455+00:00
-- url     : https://prove2.me/theorems/70c50b92-ce2f-4a10-b759-350cecce5cbf
-- title:
--   Aether Catalog definitions — Cryptography_IsogenySIDH_MontgomeryModelFibres
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.IsogenySIDH.MontgomeryModelFibres`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/IsogenySIDH/MontgomeryModelFibres.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Cryptography_IsogenySIDH_TwoIsogenyNeighbours
/-
# The six Montgomery models of one `j`-invariant, and the 6-to-3 fibration

`ModularTwoIsogeny` proved two counting *bounds*: a vertex of the 2-isogeny
graph has at most three neighbours, and a `j`-invariant has at most six
Montgomery models.  The previous cycle's Conjecture 2 asserted that both bounds
are attained and that the radical map `jQuot` fibres the six models onto the
three neighbours in pairs.  This file proves that, using the explicit second and
third Montgomery models constructed in `TwoIsogenyNeighbours`.

Given `A` with `A² ≠ 4` and the two roots `u₁ ≠ u₂` of `u² + A²u + A² = 0`, the
six Montgomery models of `E_A` are

  `± A`,  `± A₁`,  `± A₂`,   where `A₁² = tShift A u₁`, `A₂² = tShift A u₂`,

`± A₁` and `± A₂` being the models obtained by moving the two other two-torsion
points to the origin (these live over `K(√(A²-4), √(-A r - 2))`).

* `jMont_of_shift_root` — each `Aᵢ` is indeed a Montgomery model of the *same*
  curve, and is nondegenerate.
* `montgomery_models_complete` — **exactness of the bound `6`**: as soon as the
  six listed parameters are distinct, they are *all* the Montgomery models: any
  `B` with `j(E_B) = j(E_A)` and `B² ≠ 4` is one of them.
* `jQuot_of_shift_root`, `jQuot_image_of_models` — **the 6-to-3 fibration**: the
  radical map `jQuot` sends the six models onto exactly the three neighbours
  `jQuot A`, `jOther A u₁`, `jOther A u₂`, with fibres `{A, -A}`, `{A₁, -A₁}`,
  `{A₂, -A₂}` — the two members of a fibre differing by the sign of the radical,
  i.e. by the quadratic twist of the *model*.
* `two_isogeny_neighbours_card_eq_three` — **exactness of the bound `3`**: the
  vertex `j(E_A)` has exactly three neighbours in the 2-isogeny graph.
-/

set_option maxHeartbeats 1000000

namespace Cryptography.IsogenySIDH

variable {K : Type*} [Field K]

/-! ## The shifted models -/




/-! ## Exactness of the bound six -/

/-- The six candidate Montgomery models of `E_A`. -/
def montModels [DecidableEq K] (A A₁ A₂ : K) : Finset K := {A, -A, A₁, -A₁, A₂, -A₂}



/-! ## The 6-to-3 fibration -/



end Cryptography.IsogenySIDH


