-- Prove2me | Definitions.Def_Bridges_TwoTreeClosure_AscentEconomics
-- name    : Bridges_TwoTreeClosure_AscentEconomics
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:44:23.919749+00:00
-- url     : https://prove2.me/theorems/c7a5a929-93be-4e12-a7ee-7457f36b05bb
-- title:
--   Aether Catalog definitions — Bridges_TwoTreeClosure_AscentEconomics
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.TwoTreeClosure.AscentEconomics`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/TwoTreeClosure/AscentEconomics.lean by skeleton subtraction
import Mathlib

/-!
# Ascent economics: restart energy, accuracy thresholds, compounding hints

Companion to `Bridges.TwoTreeClosure.TreeCore`.  A guided ascent of the
Berggren/Price tree of height `h` whose per-step letter oracle is correct with
probability `a` succeeds with probability `a ^ h`; with restarts, the expected
number of visited nodes is the **restart energy**

`E h a = h / a ^ h = h * a ^ (-h)`.

Results proved here:

* `restartEnergy_ge_height`, `restartEnergy_strictMono_height` : `E` is at least the
  height and strictly increases with the height for any accuracy `a < 1`;
* `restartEnergy_antitone_accuracy` : `E` strictly decreases in the accuracy;
* `restartEnergy_le_iff` : the budget constraint `E h a ≤ c` is exactly `h ≤ c aʰ`;
* `accuracy_085_over_budget` / `accuracy_086_within_budget` : at height `30` and
  budget `3000` visit-equivalents the critical accuracy `α*` lies strictly between
  `0.85` and `0.86` — a rigorous version of the empirical law `α* ≥ 0.85`;
* `sequential_hints_compound` / `compound_below_saturating` : sequential hints
  compound geometrically (`a ^ h → 0`) while a saturating class hint stays put;
* `exhaustive_cost_astronomical` : the exhaustive alternative at height `30` costs
  `(3 ^ 31 - 1) / 2 > 10 ^ 14` visits, so only the guided regime is on the table.
-/

namespace TwoTreeClosure

open Filter

/-- Expected number of node visits of a restarted guided ascent of height `h` whose
per-step letter oracle has accuracy `a`. -/
noncomputable def restartEnergy (h : ℕ) (a : ℝ) : ℝ := (h : ℝ) / a ^ h






/-! ### The critical accuracy at height 30 with a budget of 3000 visits -/




/-! ### Compounding versus saturation -/




/-! ### The exhaustive alternative -/


end TwoTreeClosure


