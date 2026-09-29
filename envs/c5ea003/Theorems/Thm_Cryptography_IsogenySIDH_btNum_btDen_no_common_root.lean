-- Prove2me | Theorems.Thm_Cryptography_IsogenySIDH_btNum_btDen_no_common_root
-- name    : Cryptography.IsogenySIDH.btNum_btDen_no_common_root
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T02:41:07.573209+00:00
-- url     : https://prove2.me/theorems/1a89b045-c672-45a7-97e4-e2ac47e88037
-- title:
--   No common root.
-- statement:
--   **No common root.**  In a field whose characteristic is none of
--   `2, 3, 5, 11`, the polynomials `btNum` and `btDen` have no common root.  This is
--   the degenerate case of the cube-root branch of `backtrackPoly`, so ruling it out
--   removes `j = 0` from the exceptional set of the non-backtracking theorem.
--
--   ```lean
--   theorem Cryptography.IsogenySIDH.btNum_btDen_no_common_root{A : K} (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
--       (h5 : (5 : K) ≠ 0) (h11 : (11 : K) ≠ 0) (hn : btNum A = 0) (hd : btDen A = 0) :
--       False := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/IsogenySIDH/BacktrackingCharacteristic.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/IsogenySIDH/BacktrackingCharacteristic.lean#L59

-- Thm stub generated from Cryptography/IsogenySIDH/BacktrackingCharacteristic.lean
import Mathlib
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

theorem Cryptography.IsogenySIDH.btNum_btDen_no_common_root{A : K} (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    (h5 : (5 : K) ≠ 0) (h11 : (11 : K) ≠ 0) (hn : btNum A = 0) (hd : btDen A = 0) :
    False := by sorry
