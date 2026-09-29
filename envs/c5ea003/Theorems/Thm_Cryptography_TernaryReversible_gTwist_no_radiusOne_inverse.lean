-- Prove2me | Theorems.Thm_Cryptography_TernaryReversible_gTwist_no_radiusOne_inverse
-- name    : Cryptography.TernaryReversible.gTwist_no_radiusOne_inverse
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T02:45:48.806026+00:00
-- url     : https://prove2.me/theorems/a9f5e69e-7d9a-40ac-8f41-338799d9e1b7
-- title:
--   No radius-one inverse automaton.
-- statement:
--   **No radius-one inverse automaton.** There is no local rule `d` whose global maps
--   invert those of `gTwist` on all cycles.
--
--   ```lean
--   theorem Cryptography.TernaryReversible.gTwist_no_radiusOne_inverse:
--       ¬ ∃ d : LocalRule, ∀ (n : ℕ) (s : ZMod n → Alph),
--           globalMap d (globalMap gTwist s) = s := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/TernaryReversible/InverseRadius.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/TernaryReversible/InverseRadius.lean#L136

-- Thm stub generated from Cryptography/TernaryReversible/InverseRadius.lean
import Mathlib
import Definitions.Def_Cryptography_TernaryReversible_Core
import Definitions.Def_Cryptography_TernaryReversible_InverseRadius

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

open Cryptography
open TernaryReversible






/-! ## The inverse is not radius one -/

theorem Cryptography.TernaryReversible.gTwist_no_radiusOne_inverse:
    ¬ ∃ d : LocalRule, ∀ (n : ℕ) (s : ZMod n → Alph),
        globalMap d (globalMap gTwist s) = s := by sorry
