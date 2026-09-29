-- Prove2me | Theorems.Thm_TraceBattery_H_two_values
-- name    : TraceBattery.H_two_values
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T04:54:00.149436+00:00
-- url     : https://prove2.me/theorems/81098356-b145-4d3c-ba7b-aa27c375571c
-- title:
--   A statistic attaining exactly two readings has empirical entropy equal to
-- statement:
--   A statistic attaining exactly two readings has empirical entropy equal to
--   the binary entropy of the fraction sitting in the first class.
--
--   ```lean
--   theorem TraceBattery.H_two_values(f : Ω → α) {a b : α} (hab : a ≠ b) (himg : img f = {a, b}) :
--       H f = Real.binEntropy ((cnt f a : ℝ) / (Fintype.card Ω : ℝ)) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Speculative/AutoResearch/TraceBatteryWall.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Speculative/AutoResearch/TraceBatteryWall.lean#L39

-- Thm stub generated from Speculative/AutoResearch/TraceBatteryWall.lean
import Mathlib
import Definitions.Def_Speculative_AutoResearch_TraceBatteryEntropy
/-
# TRACE-BATTERY, part III: the which-factor wall is an imbalance meter

The round-30 experiment reports a *which-factor wall* at `0.4677` bits: the
binary "which factor?" statistic never carries more than that, a value the paper
attributes to sparse-table bias.  This file explains what such a number can and
cannot mean.

A binary statistic on a finite population is completely described, as far as
capacity is concerned, by the fraction `p` of the population in its smaller
class:

* `TraceBattery.H_two_values` — for a statistic attaining exactly the two
  readings `a ≠ b`, the empirical entropy equals Mathlib's binary entropy
  `Real.binEntropy` of the fraction of the `a`-class.  So the wall value is a
  *measurement of class imbalance*, nothing else.
* `TraceBattery.binary_capacity_lt_of_lt` — on the balanced side `[0, 1/2]` the
  capacity is strictly increasing in the minority fraction.
* `TraceBattery.wall_determines_imbalance` — hence a reported wall value pins
  the imbalance down uniquely: two binary statistics with equal capacity and
  minority fractions in `[0, 1/2]` have the *same* fraction.
* `TraceBattery.binary_capacity_le_one_bit` — and the wall can never exceed one
  bit, so any reported value below `1` is admissible; only the *inverted*
  fraction carries information.

All statements are sorry-free.
-/

open TraceBattery

open Finset


variable {Ω : Type*} [Fintype Ω] [Nonempty Ω] {α : Type*}

open Classical in

theorem TraceBattery.H_two_values(f : Ω → α) {a b : α} (hab : a ≠ b) (himg : img f = {a, b}) :
    H f = Real.binEntropy ((cnt f a : ℝ) / (Fintype.card Ω : ℝ)) := by sorry
