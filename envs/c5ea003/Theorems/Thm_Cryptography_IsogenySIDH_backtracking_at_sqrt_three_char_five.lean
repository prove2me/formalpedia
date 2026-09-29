-- Prove2me | Theorems.Thm_Cryptography_IsogenySIDH_backtracking_at_sqrt_three_char_five
-- name    : Cryptography.IsogenySIDH.backtracking_at_sqrt_three_char_five
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T02:41:31.107869+00:00
-- url     : https://prove2.me/theorems/ccf3d065-27b9-47c3-94e3-9d2997dffa9f
-- title:
--   Characteristic `5`: backtracking at `j = 0`.
-- statement:
--   **Characteristic `5`: backtracking at `j = 0`.**  In characteristic `5` any
--   `A` with `A² = 3` satisfies `btNum A = 60A + 135 = 0` and `btDen A = 0`, so
--   backtracking occurs at `j = 0`.  Hence the hypothesis `(5 : K) ≠ 0` in
--   `radical_two_step_nonbacktracking_sharp` is necessary.
--
--   ```lean
--   theorem Cryptography.IsogenySIDH.backtracking_at_sqrt_three_char_five{A α : K} (h5 : (5 : K) = 0)
--       (hA : A ^ 2 = 3) (hα : α ≠ 0) (hsq : α ^ 2 = A + 2) :
--       jQuot (radTwoParam A α) = jMont A ∧ jMont A = 0 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/IsogenySIDH/BacktrackingCharacteristic.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/IsogenySIDH/BacktrackingCharacteristic.lean#L215

-- Thm stub generated from Cryptography/IsogenySIDH/BacktrackingCharacteristic.lean
import Mathlib
import Definitions.Def_Cryptography_IsogenySIDH_ModularTwoIsogeny
import Definitions.Def_Cryptography_IsogenySIDH_RadicalMontgomeryFormula
import Definitions.Def_Cryptography_IsogenySIDH_RadicalNonBacktracking
/-
# The exceptional `j`-invariant `0` is a characteristic phenomenon

`RadicalNonBacktracking.lean` proved that, over a field containing no primitive
cube root of unity, a radical 2-isogeny walk can return to its starting
`j`-invariant after two steps only when

`j ∈ {0, -3375, 287496}`,

and it exhibited backtracking at `-3375` and at `287496`.  The value `0` was
left as a *possible* exception: it enters the classification only through the
degenerate case `btDen A = 0` of the cube-root branch, and the previous cycle's
`FUTURE_DIRECTIONS.md` conjectured (Conjecture 2) that it too is attained.

This file settles that question, and the answer is a **correction** of the
conjecture:

* `btNum_btDen_no_common_root` — the two comparison polynomials
  `btNum A = A² + 60A + 132` and `btDen A = 4(A²-3)(A-2)` have **no common
  root** in any field whose characteristic avoids `2, 3, 5, 11`.  The proof is
  an explicit elimination: a common root forces `A = 2` (excluded, since
  `btNum 2 = 2⁸`) or `A² = 3` together with `15(4A+9) = 0`, whence
  `16·3 = (4A)² = 81`, i.e. `33 = 0`.
* `radical_two_step_nonbacktracking_sharp` — consequently the exceptional set
  shrinks: away from characteristic `2, 3, 5, 11`, and over a field with no
  primitive cube root of unity, two-step backtracking forces
  `j ∈ {-3375, 287496}`.  The value `0` is **not** exceptional.
* `radChain_two_step_nonbacktracking_sharp` — the walk-level version.
* Sharpness in the excluded characteristics: `backtracking_at_zero_char_three`
  and `backtracking_at_sqrt_three_char_five` show that in characteristic `3`
  (at `A = 0`) and in characteristic `5` (at `A² = 3`) backtracking at `j = 0`
  really does occur, so the hypotheses `(3 : K) ≠ 0` and `(5 : K) ≠ 0` cannot be
  dropped; `backtracking_at_six_char_eleven` shows that in characteristic `11`
  the `j = 0` locus `A² = 3` collapses onto the principal branch `A = 6`, which
  is why `11` also has to be excluded from the elimination even though it
  produces no new exceptional value.
* `char_five_backtracking_exists` makes the characteristic-`5` counterexample
  unconditional by producing it over `AlgebraicClosure (ZMod 5)`.

So the final statement of the two-step non-backtracking theorem is: outside of
characteristics `2, 3, 5, 11`, and outside of fields containing a primitive cube
root of unity, **exactly two** `j`-invariants can backtrack, namely the CM
values `-3375` (discriminant `-7`) and `287496` (discriminant `-16`).
-/

set_option maxHeartbeats 1000000

open Cryptography.IsogenySIDH

variable {K : Type*} [Field K]

/-! ## Eliminating the degenerate branch -/



/-! ## The sharpened classification -/





/-! ## Sharpness in the excluded characteristics -/

theorem Cryptography.IsogenySIDH.backtracking_at_sqrt_three_char_five{A α : K} (h5 : (5 : K) = 0)
    (hA : A ^ 2 = 3) (hα : α ≠ 0) (hsq : α ^ 2 = A + 2) :
    jQuot (radTwoParam A α) = jMont A ∧ jMont A = 0 := by sorry
