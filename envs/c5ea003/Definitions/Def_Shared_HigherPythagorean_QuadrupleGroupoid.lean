-- Prove2me | Definitions.Def_Shared_HigherPythagorean_QuadrupleGroupoid
-- name    : Shared_HigherPythagorean_QuadrupleGroupoid
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T14:55:18.904594+00:00
-- url     : https://prove2.me/theorems/30b296cb-a615-45f9-b587-c716801d0a6c
-- title:
--   Aether Catalog definitions — Shared_HigherPythagorean_QuadrupleGroupoid
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.HigherPythagorean.QuadrupleGroupoid`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/HigherPythagorean/QuadrupleGroupoid.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Shared_HigherPythagorean_LorentzCore
import Definitions.Def_Shared_HigherPythagorean_QuadrupleTree
import Definitions.Def_Shared_Ispythquadruple_IsPythQuadruple

/-!
# The Pythagorean quadruple groupoid

This is the dimension-three analogue of the Berggren groupoid of the catalog
(`Catalog/Pythagorean/BerggrenGroupoid.lean`), together with the structural theorem that is
*not* available in dimension two by those methods: the groupoid acts **transitively** on the
primitive Pythagorean quadruples of the positive cone.

* `moveR`, `moveN`, `moveS12`, `moveS23` : the generating moves (all-ones Lorentz reflection,
  one sign change, two transpositions).  Each is an involution, hence a bijection.
* `QuadMove` / `QuadConnected` : the generated groupoid relation.
* `qLorentz_of_connected`, `qcontent_of_connected` : the Lorentz form and the content are
  groupoid invariants.
* `quadConnected_of_prim` : **transitivity on primitive quadruples** — any two primitive
  Pythagorean quadruples with non-negative space coordinates and positive height are connected.
* `not_connected_of_content_ne` : the invariants are effective — quadruples of different content
  are never connected (e.g. `(1,2,2,3)` and `(2,4,4,6)`).
-/

namespace HigherPythagorean

/-- A quadruple, viewed as a point of the integral Lorentz space of signature `(3,1)`. -/
abbrev Quad := ℤ × ℤ × ℤ × ℤ

/-- The Lorentz form of a quadruple. -/
def qLorentz (p : Quad) : ℤ := p.1 ^ 2 + p.2.1 ^ 2 + p.2.2.1 ^ 2 - p.2.2.2 ^ 2

/-- The content of a quadruple. -/
def qcontent (p : Quad) : ℕ := content p.1 p.2.1 p.2.2.1 p.2.2.2


/-! ## The generating moves -/

/-- The all-ones Lorentz reflection. -/
def moveR (p : Quad) : Quad :=
  (p.1 - qk p.1 p.2.1 p.2.2.1 p.2.2.2, p.2.1 - qk p.1 p.2.1 p.2.2.1 p.2.2.2,
    p.2.2.1 - qk p.1 p.2.1 p.2.2.1 p.2.2.2, p.2.2.2 - qk p.1 p.2.1 p.2.2.1 p.2.2.2)

/-- The sign change of the first coordinate. -/
def moveN (p : Quad) : Quad := (-p.1, p.2.1, p.2.2.1, p.2.2.2)

/-- The transposition of the first two space coordinates. -/
def moveS12 (p : Quad) : Quad := (p.2.1, p.1, p.2.2.1, p.2.2.2)

/-- The transposition of the last two space coordinates. -/
def moveS23 (p : Quad) : Quad := (p.1, p.2.2.1, p.2.1, p.2.2.2)









/-! ## Invariance -/









/-! ## The groupoid -/

/-- One generating move of the quadruple groupoid. -/
inductive QuadMove : Quad → Quad → Prop
  | r (p : Quad) : QuadMove p (moveR p)
  | n (p : Quad) : QuadMove p (moveN p)
  | s12 (p : Quad) : QuadMove p (moveS12 p)
  | s23 (p : Quad) : QuadMove p (moveS23 p)

/-- Two quadruples are connected when one is carried to the other by a finite sequence of
generating moves and their inverses: the morphism relation of the generated groupoid. -/
def QuadConnected : Quad → Quad → Prop := Relation.EqvGen QuadMove










/-! ## Transitivity on primitive quadruples -/





end HigherPythagorean


