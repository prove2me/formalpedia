-- Prove2me | Theorems.Thm_PythHydra_parent_addr_cons
-- name    : PythHydra.parent_addr_cons
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-17T13:11:37.424053+00:00
-- url     : https://prove2.me/theorems/296de97b-2285-4d1c-a6db-2a71bbeb25d1
-- title:
--   Reading off the last letter: the parent map deletes the head of the address.
-- statement:
--   **Reading off the last letter**: the parent map deletes the head of the address.
--
--   ```lean
--   theorem PythHydra.parent_addr_cons(s : BStep) (w : List BStep) :
--       parent (addr (s :: w)).1 (addr (s :: w)).2.1 (addr (s :: w)).2.2 = addr w := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/PythagoreanHydra/BerggrenAddress.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/PythagoreanHydra/BerggrenAddress.lean#L149

-- Thm stub generated from Geometry/PythagoreanHydra/BerggrenAddress.lean
import Mathlib
import Definitions.Def_Geometry_PythagoreanHydra_BerggrenAddress
import Definitions.Def_Geometry_PythagoreanHydra_BerggrenDescent

/-!
# The address function of the Berggren tree

The second front of the research mission asks whether the first-order theory of the
Berggren tree *with its address function* (word ↦ triple) can encode Diophantine
machines, producing a Matiyasevich-style undecidability phenomenon.

Here we prove the opposite, in the strongest form available: the address function

`addr : List BStep → ℤ × ℤ × ℤ`,  `addr [] = (3,4,5)`,  `addr (s :: w) = bergₛ (addr w)`

is a **computable bijection** from the free monoid on three letters onto the set of
primitive Pythagorean triples with odd first leg (`addr_bijective`), its inverse is
computed by the inverse Berggren moves (`parent_addr_cons`), and membership is decidable
(`decidableReach` in `BerggrenDescent.lean`).  The Berggren tree is therefore *free*: no
two addresses collide, and the word can be read off from the triple by descent.  In
particular the address relation is decidable, so no undecidable Diophantine phenomenon
can be encoded in it.

The key computation is that the coordinates `uu`, `vv` used by the parent map recover the
parent triple exactly:  `uu (bergA a b c) = a`, `vv (bergA a b c) = -b`, and similarly
`(a, b)` for `bergB` and `(-a, b)` for `bergC` — the *sign pattern* of `(uu, vv)` is
precisely the label of the last Berggren move.
-/

open PythHydra

/-! ### Recovering the last move from the sign pattern -/













/-! ### Hypotenuse estimates -/





/-! ### The address function -/

theorem PythHydra.parent_addr_cons(s : BStep) (w : List BStep) :
    parent (addr (s :: w)).1 (addr (s :: w)).2.1 (addr (s :: w)).2.2 = addr w := by sorry
