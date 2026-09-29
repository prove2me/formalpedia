-- Prove2me | Theorems.Thm_ThreeCubes_card_repsBox_one
-- name    : ThreeCubes.card_repsBox_one
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:11:36.198658+00:00
-- url     : https://prove2.me/theorems/dcf1442d-13d6-4d60-9058-bef1d2e48342
-- title:
--   `1` has at least `2T+1` representations of height `≤ 12T⁴ + 9T³ + 3T + 1`.
-- statement:
--   **`1` has at least `2T+1` representations of height `≤ 12T⁴ + 9T³ + 3T + 1`.**
--   Since the box radius is `≍ T⁴`, this gives `≫ B^{1/4}` representations of height `≤ B`,
--   far more than the conjectured `log B` for generic `n`.
--
--   ```lean
--   theorem ThreeCubes.card_repsBox_one(T : ℕ) :
--       2 * T + 1 ≤ (repsBox 1 (12 * (T : ℤ) ^ 4 + 9 * (T : ℤ) ^ 3 + 3 * (T : ℤ) + 1)).card := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/Counting.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/Counting.lean#L47

-- Thm stub generated from Probability/Counting.lean
import Mathlib
import Definitions.Def_Probability_Basic
import Definitions.Def_Probability_Counting

/-!
# Counting representations: `1` and `2` are exceptional

Heath-Brown's conjecture predicts that for a *generic* admissible `n` the number of
representations `n = x³ + y³ + z³` with `max(|x|,|y|,|z|) ≤ B` grows like `c_n log B`.  The
integers `1` and `2` are famously exceptional: the classical one-parameter families give
`≫ B^{1/4}` and `≫ B^{1/3}` representations respectively, which is vastly more than
logarithmic.

This file makes those lower bounds explicit and formal:

* `ThreeCubes.card_repsBox_one` : at least `2T+1` representations of `1` inside the box of
  radius `12T⁴ + 9T³ + 3T + 1`, i.e. `≫ B^{1/4}` representations of height `≤ B`;
* `ThreeCubes.card_repsBox_two` : at least `2T+1` representations of `2` inside the box of
  radius `6T³ + 6T² + 1`, i.e. `≫ B^{1/3}` representations of height `≤ B`.
-/

open ThreeCubes

theorem ThreeCubes.card_repsBox_one(T : ℕ) :
    2 * T + 1 ≤ (repsBox 1 (12 * (T : ℤ) ^ 4 + 9 * (T : ℤ) ^ 3 + 3 * (T : ℤ) + 1)).card := by sorry
