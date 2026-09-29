-- Prove2me | Definitions.Def_Bridges_TwoTreeClosure_RepresentationOrbit
-- name    : Bridges_TwoTreeClosure_RepresentationOrbit
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:44:55.289548+00:00
-- url     : https://prove2.me/theorems/76152e1e-b01a-4951-b378-cc947f26a4dc
-- title:
--   Aether Catalog definitions — Bridges_TwoTreeClosure_RepresentationOrbit
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.TwoTreeClosure.RepresentationOrbit`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/TwoTreeClosure/RepresentationOrbit.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Bridges_TwoTreeClosure_TreeCore

/-!
# Magnitude collisions need not split the ascent letter — the orbit conjecture is false

`Bridges.TwoTreeClosure.TreeCore` proves *magnitude blindness* by exhibiting a family
of hypotenuse collisions whose two nodes carry **different** ascent letters
(`letterOf_blind_of_magnitude`).  The natural strengthening — proposed as direction 1
of the previous cycle's `FUTURE_DIRECTIONS.md` — was the *orbit conjecture*:

> whenever `N` has two essentially distinct primitive representations as a sum of two
> coprime squares, the two corresponding tree nodes carry **different** ascent letters,

which would have turned magnitude blindness into a structure theorem and, read the
other way round, would have given a genuine one-bit signal ("the letters of a
collision are never equal").

This file **refutes** that conjecture with an explicit infinite family coming from the
Sophie Germain identity `u⁴ + 4 = (u² - 2u + 2)(u² + 2u + 2)`.  Writing `u = 2s + 7`,

* `sgN s = (4s² + 28s + 49)² + 4 = (4s² + 24s + 37)(4s² + 32s + 65)` is composite;
* it is the hypotenuse of the two distinct primitive nodes
  `sgP s = (4s² + 28s + 47, 4s + 14)` (the `(u² - 2, 2u)` representation) and
  `sgQ s = (4s² + 28s + 49, 2)` (the `(u², 2)` representation);
* and **both** nodes have ascent letter `C`, because `u² - 2 > 3 · 2u` for `u ≥ 7`.

Consequences.

* `orbit_letter_separation_false` : the orbit conjecture is false.
* `collision_letter_dichotomy` : *both* phenomena occur above every bound — there are
  hypotenuse collisions with equal letters and hypotenuse collisions with distinct
  letters.  So "does `N` admit a collision?" carries no letter information at all: the
  letter multiset of the representations of `N` is not a function of the collision
  pattern, and the residual positional content of the tree is not addressable by
  counting representations.

The smallest member (`s = 0`) is `2405 = 5 · 13 · 37 = 47² + 14² = 49² + 2²`, with
`47 > 3 · 14` and `49 > 3 · 2`: two `C`'s.
-/

namespace TwoTreeClosure

/-! ### The Sophie Germain collision family -/

/-- First node of the collision family: the `(u² - 2, 2u)` representation, `u = 2s+7`. -/
def sgP (s : ℕ) : ℕ × ℕ := (4 * s ^ 2 + 28 * s + 47, 4 * s + 14)

/-- Second node of the collision family: the `(u², 2)` representation, `u = 2s+7`. -/
def sgQ (s : ℕ) : ℕ × ℕ := (4 * s ^ 2 + 28 * s + 49, 2)

/-- The common hypotenuse of the two nodes, `u⁴ + 4` for `u = 2s + 7`. -/
def sgN (s : ℕ) : ℕ := (4 * s ^ 2 + 28 * s + 49) ^ 2 + 4





/-! ### Both members are genuine primitive nodes -/




/-! ### Both members carry the same ascent letter -/




/-! ### The refutation -/






end TwoTreeClosure


