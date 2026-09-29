-- Prove2me | Theorems.Thm_Cryptography_IsogenySIDH_radical_two_step_nonbacktracking_sharp
-- name    : Cryptography.IsogenySIDH.radical_two_step_nonbacktracking_sharp
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T02:44:01.274498+00:00
-- url     : https://prove2.me/theorems/376a55ca-d292-4661-8a90-31915dce4b46
-- title:
--   Sharpened two-step non-backtracking.
-- statement:
--   **Sharpened two-step non-backtracking.**  Over a field of characteristic
--   different from `2, 3, 5, 11` and containing no primitive cube root of unity, a
--   radical 2-isogeny step can return the walk to its starting `j`-invariant after
--   two steps only when that `j`-invariant is `-3375` or `287496`.  Compared with
--   `radical_two_step_nonbacktracking` the value `0` has been removed from the
--   exceptional set — and by `backtracking_at_sqrt_three_char_five` below, that
--   removal is exactly as strong as it can be.
--
--   ```lean
--   theorem Cryptography.IsogenySIDH.radical_two_step_nonbacktracking_sharp{A α : K} (h2 : (2 : K) ≠ 0)
--       (h3 : (3 : K) ≠ 0) (h5 : (5 : K) ≠ 0) (h11 : (11 : K) ≠ 0)
--       (hcube : ∀ t : K, t ^ 2 + t + 1 ≠ 0) (hα : α ≠ 0) (hsq : α ^ 2 = A + 2)
--       (hd : A ^ 2 - 4 ≠ 0) (hj1 : jMont A ≠ -3375) (hj2 : jMont A ≠ 287496) :
--       jQuot (radTwoParam A α) ≠ jMont A := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/IsogenySIDH/BacktrackingCharacteristic.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/IsogenySIDH/BacktrackingCharacteristic.lean#L103

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

theorem Cryptography.IsogenySIDH.radical_two_step_nonbacktracking_sharp{A α : K} (h2 : (2 : K) ≠ 0)
    (h3 : (3 : K) ≠ 0) (h5 : (5 : K) ≠ 0) (h11 : (11 : K) ≠ 0)
    (hcube : ∀ t : K, t ^ 2 + t + 1 ≠ 0) (hα : α ≠ 0) (hsq : α ^ 2 = A + 2)
    (hd : A ^ 2 - 4 ≠ 0) (hj1 : jMont A ≠ -3375) (hj2 : jMont A ≠ 287496) :
    jQuot (radTwoParam A α) ≠ jMont A := by sorry
