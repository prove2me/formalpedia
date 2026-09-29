-- Prove2me | Theorems.Thm_TwoTreeClosure_hyp_sgQ
-- name    : TwoTreeClosure.hyp_sgQ
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:24:27.563351+00:00
-- url     : https://prove2.me/theorems/f02fb247-f1d8-4931-a65a-cd1c8c48a2b5
-- title:
--   Hyp sgQ
-- statement:
--   Formal statement of `TwoTreeClosure.hyp_sgQ` from the Aether Catalog (Bridges). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem TwoTreeClosure.hyp_sgQ(s : ℕ) : hyp (sgQ s).1 (sgQ s).2 = sgN s := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/TwoTreeClosure/RepresentationOrbit.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/TwoTreeClosure/RepresentationOrbit.lean#L73

-- Thm stub generated from Bridges/TwoTreeClosure/RepresentationOrbit.lean
import Mathlib
import Definitions.Def_Bridges_TwoTreeClosure_RepresentationOrbit
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

open TwoTreeClosure

/-! ### The Sophie Germain collision family -/

theorem TwoTreeClosure.hyp_sgQ(s : ℕ) : hyp (sgQ s).1 (sgQ s).2 = sgN s := by sorry
