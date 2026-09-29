-- Prove2me | Definitions.Def_Cryptography_TernaryReversible_InverseRadius
-- name    : Cryptography_TernaryReversible_InverseRadius
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T02:23:57.05255+00:00
-- url     : https://prove2.me/theorems/7e1effc9-50fe-4e7c-9dba-d2a7b98b1723
-- title:
--   Aether Catalog definitions — Cryptography_TernaryReversible_InverseRadius
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.TernaryReversible.InverseRadius`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/TernaryReversible/InverseRadius.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Cryptography_TernaryReversible_Core

/-!
# A reversible ternary radius-one rule whose inverse is not radius one

The refutation in `Cryptography.TernaryReversible.Refutation` produces rules that are
bijective on every cycle but still decode with a *radius-one* inverse (they are
involutions).  This file goes one step further and exhibits a rule for which local
reversibility is genuinely non-local: the **conditional-transposition rule**

`gTwist a b c = if (b ≠ 0 ∧ c = 2) then swap01 a else a`,

which copies the left neighbour, transposing the values `0` and `1` exactly when the
pattern `(b ≠ 0, c = 2)` occurs to its right.

## Main results

* `gTwist_decoder4` / `gTwist_cycleBijective`: `gTwist` is bijective on every nonempty
  finite cycle, because a window-*four* decoder reconstructs each cell from the four
  output cells to its right.
* `gTwist_no_window3_decoder`: **no** window-three decoder exists, at *any* of the five
  possible offsets; so the inverse automaton has neighbourhood width at least four.
* `gTwist_no_radiusOne_inverse`: in particular `gTwist` has no radius-one inverse
  cellular automaton.
* `gTwist_deps`: `gTwist` also uses two cells of its window, hence is one more
  counterexample to the classification claim, of a shape different from the
  sign-twisted involutions.

The mechanism: the transposition `swap01` fixes the letter `2`, so the positions
carrying `2` are visible in the output, but deciding whether the *condition* fired at a
cell requires knowing whether its right neighbour is nonzero, which in turn requires
looking one cell further right.  The information needed to invert therefore travels a
bounded but strictly larger distance than the rule itself.
-/

namespace Cryptography
namespace TernaryReversible

/-- The transposition of `0` and `1` fixing `2`. -/
def swap01 (x : Alph) : Alph := if x = 2 then 2 else 1 - x

/-- The conditional-transposition rule. -/
def gTwist : LocalRule := fun a b c => if b ≠ 0 ∧ c = 2 then swap01 a else a

/-- The window-four decoder for `gTwist`: it recovers the *leftmost* cell of a window
from the four output cells it determines. -/
def dTwist (u₀ u₁ u₂ u₃ : Alph) : Alph :=
  if u₂ = 2 ∧ (if u₃ = 2 then u₁ ≠ 1 else u₁ ≠ 0) then swap01 u₀ else u₀



/-! ## The inverse is not radius one -/







/-- Two configurations on the five-cycle that a radius-one inverse could not separate:
the constant `0` configuration and `(0,0,1,1,2)` have the same image in positions
`1, 2, 3` but differ in position `2`. -/
def conf5 : ZMod 5 → Alph := fun i => if i = 2 then 1 else if i = 3 then 1 else
  if i = 4 then 2 else 0


/-! ## `gTwist` is a counterexample of a new shape -/






end TernaryReversible
end Cryptography


