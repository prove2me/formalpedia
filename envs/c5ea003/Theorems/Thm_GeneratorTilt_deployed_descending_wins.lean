-- Prove2me | Theorems.Thm_GeneratorTilt_deployed_descending_wins
-- name    : GeneratorTilt.deployed_descending_wins
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:58:31.480507+00:00
-- url     : https://prove2.me/theorems/4b149066-b896-44b0-86f1-3a96a233f3a7
-- title:
--   Deployment theorem.
-- statement:
--   **Deployment theorem.**  Let `N = p q` with `0 < p ≤ q` and prime ratio `r = q/p`.  If
--   `N` is large enough that `1 ≤ 2 · margin r · √N` — possible for all large `N` exactly when
--   `r` is below the critical ratio, by `margin_pos_iff_top_heavy` — then on the *integer*
--   window `[⌈√(N/2)⌉, ⌊√N⌋]` the sqrt-descending scan strictly beats the window-ascending scan:
--   `⌈√(N/2)⌉ + ⌊√N⌋ < 2p`.
--
--   This is the refutation in deployable form: for a generator whose ratio concentrates below
--   `24 - 16√2 ≈ 1.3726` (in particular the observed deployed-style concentration near `1`),
--   window-ascending loses on every sufficiently large key.
--
--   ```lean
--   theorem GeneratorTilt.deployed_descending_wins{n : ℤ} {q : ℝ} (hp : 0 < (n : ℝ)) (hq : 0 < q)
--       (hN : 1 ≤ 2 * margin (q / (n : ℝ)) * Real.sqrt ((n : ℝ) * q)) :
--       descCost ⌊Real.sqrt ((n : ℝ) * q)⌋ n < ascCost ⌈Real.sqrt ((n : ℝ) * q / 2)⌉ n := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/GeneratorTiltSynthesis.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/GeneratorTiltSynthesis.lean#L96

-- Thm stub generated from Novelty/GeneratorTiltSynthesis.lean
import Mathlib
import Definitions.Def_Novelty_GeneratorTiltRatio
import Definitions.Def_Novelty_GeneratorTiltSynthesis
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

open GeneratorTilt

open Finset

/-! ## Debt 1: rounding to the integer window -/


/-! ## Debt 2: aggregating over per-key windows -/

variable {ι : Type*}





/-! ## The margin of a ratio -/




/-! ## The deployed statement -/

theorem GeneratorTilt.deployed_descending_wins{n : ℤ} {q : ℝ} (hp : 0 < (n : ℝ)) (hq : 0 < q)
    (hN : 1 ≤ 2 * margin (q / (n : ℝ)) * Real.sqrt ((n : ℝ) * q)) :
    descCost ⌊Real.sqrt ((n : ℝ) * q)⌋ n < ascCost ⌈Real.sqrt ((n : ℝ) * q / 2)⌉ n := by sorry
