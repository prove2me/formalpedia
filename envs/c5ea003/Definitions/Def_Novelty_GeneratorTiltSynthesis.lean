-- Prove2me | Definitions.Def_Novelty_GeneratorTiltSynthesis
-- name    : Novelty_GeneratorTiltSynthesis
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:28:32.997087+00:00
-- url     : https://prove2.me/theorems/c5b36f51-ff00-4260-bace-400891e23166
-- title:
--   Aether Catalog definitions — Novelty_GeneratorTiltSynthesis
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.GeneratorTiltSynthesis`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/GeneratorTiltSynthesis.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Novelty_GeneratorTiltRatio
import Definitions.Def_Novelty_GeneratorTiltWindow
/-
# Synthesis: from the generator's ratio law to integer scan costs

`Novelty.GeneratorTiltWindow` decides the scan-order contest from the mean tilt of a pool;
`Novelty.GeneratorTiltRatio` computes the tilt from the generator's prime ratio.  This file
joins the two layers and pays the two debts that the idealised layers leave open:

1. **Rounding.**  A real scan runs over the *integer* window `[⌈√(N/2)⌉, ⌊√N⌋]`, not the real
   interval.  `descCost_lt_ascCost_of_real_margin` shows a half-step margin is enough to
   transfer the real comparison to the integer one.
2. **Per-key windows.**  Different keys have different windows, so the pool statement of
   `GeneratorTiltWindow` (one common window) is not directly applicable.
   `totalDescVar_lt_totalAscVar` proves the aggregation with a window per key.

The headline result is `deployed_descending_wins`: for a semiprime `N = p q` whose prime
ratio is *below* the critical ratio `24 - 16√2`, all sufficiently large `N` have
`⌈√(N/2)⌉ + ⌊√N⌋ < 2p`, i.e. the sqrt-descending scan strictly beats the window-ascending
scan on the true integer window — with an explicit threshold
`√N ≥ 1 / (2 · margin r)` where `margin r = r^{-1/2} - (1 + 2^{-1/2})/2` is positive exactly
in the top-heavy regime (`margin_pos_iff_top_heavy`).

Consequence for the Λ-channel question: a window-ascending advantage is *not* a consequence
of balance; it requires the generator's ratio mass to sit above `24 - 16√2 ≈ 1.3726`, and a
deployed-style concentration of the ratio near `1` is adversarial to it.
-/

namespace GeneratorTilt

open Finset

/-! ## Debt 1: rounding to the integer window -/


/-! ## Debt 2: aggregating over per-key windows -/

variable {ι : Type*}

/-- Total ascending cost with a window `[a i, b i]` per key. -/
def totalAscVar (s : Finset ι) (a d : ι → ℤ) : ℤ := ∑ i ∈ s, ascCost (a i) (d i)

/-- Total descending cost with a window `[a i, b i]` per key. -/
def totalDescVar (s : Finset ι) (b d : ι → ℤ) : ℤ := ∑ i ∈ s, descCost (b i) (d i)



/-! ## The margin of a ratio -/

/-- The margin by which a ratio is top-heavy: `r^{-1/2} - (1 + 2^{-1/2})/2`. -/
noncomputable def margin (r : ℝ) : ℝ := 1 / Real.sqrt r - (1 + 1 / Real.sqrt 2) / 2



/-! ## The deployed statement -/



/-! ## The scoped final statement -/


end GeneratorTilt


