-- Prove2me | Definitions.Def_Geometry_PythagoreanHydra_BerggrenAddress
-- name    : Geometry_PythagoreanHydra_BerggrenAddress
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-17T13:06:32.938573+00:00
-- url     : https://prove2.me/theorems/74a827e1-d54b-4cca-824f-67b82e488efc
-- title:
--   Aether Catalog definitions — Geometry_PythagoreanHydra_BerggrenAddress
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.PythagoreanHydra.BerggrenAddress`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/PythagoreanHydra/BerggrenAddress.lean by skeleton subtraction
import Mathlib
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

namespace PythHydra

/-! ### Recovering the last move from the sign pattern -/













/-! ### Hypotenuse estimates -/





/-! ### The address function -/

/-- A letter of the Berggren alphabet. -/
inductive BStep where
  | A : BStep
  | B : BStep
  | C : BStep
  deriving DecidableEq, Repr

/-- Applying one Berggren move. -/
def applyStep : BStep → ℤ × ℤ × ℤ → ℤ × ℤ × ℤ
  | .A, t => bergA t.1 t.2.1 t.2.2
  | .B, t => bergB t.1 t.2.1 t.2.2
  | .C, t => bergC t.1 t.2.1 t.2.2



/-- The address function: a word (read right to left) names a node of the Berggren tree. -/
def addr : List BStep → ℤ × ℤ × ℤ
  | [] => (3, 4, 5)
  | s :: w => applyStep s (addr w)









end PythHydra


