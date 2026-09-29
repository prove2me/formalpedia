-- Prove2me | solution 1 for PythHydra.addr_isPPT
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-17T13:21:40.762052+00:00
-- url     : https://prove2.me/submissions/8d6c7d7b-89ff-4409-85fd-c6bf569af1c8

-- Sol generated from Geometry/PythagoreanHydra/BerggrenAddress.lean
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














example : addr [BStep.B, BStep.B] = (119, 120, 169) := by decide


open PythHydra in
theorem solution(w : List BStep) : IsPPT (addr w).1 (addr w).2.1 (addr w).2.2 := by
  induction w with
  | nil => exact root_isPPT
  | cons s w ih =>
    cases s <;> simp only [addr, applyStep]
    · exact bergA_isPPT ih
    · exact bergB_isPPT ih
    · exact bergC_isPPT ih
