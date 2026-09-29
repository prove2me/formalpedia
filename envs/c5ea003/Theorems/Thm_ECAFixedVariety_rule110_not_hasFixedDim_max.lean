-- Prove2me | Theorems.Thm_ECAFixedVariety_rule110_not_hasFixedDim_max
-- name    : ECAFixedVariety.rule110_not_hasFixedDim_max
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:32:51.849194+00:00
-- url     : https://prove2.me/theorems/caf09371-1299-441e-8f05-939408f0a812
-- title:
--   Rule 110 (Wolfram class 4) does not have the maximal fixed-point
-- statement:
--   Rule 110 (Wolfram class 4) does **not** have the maximal fixed-point
--   dimension `n` predicted by the conjecture, for any `n ≥ 1`.
--
--   ```lean
--   theorem ECAFixedVariety.rule110_not_hasFixedDim_max(n : ℕ) (hn : 1 ≤ n) : ¬ HasFixedDim 110 n n := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/ECAFixedVarietyRule110.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/ECAFixedVarietyRule110.lean#L88

-- Thm stub generated from Novelty/ECAFixedVarietyRule110.lean
import Mathlib
import Definitions.Def_Novelty_ECAFixedVarietyCore

/-!
# Rule 110 has a rigid, zero-dimensional fixed-point variety

The headline conjecture under test asserts that the dimension of the
fixed-point variety `V(f) = {s : f(s) = s}` of an elementary cellular automaton
measures its Wolfram complexity class, with the Turing-complete Rule 110
attaining the maximal dimension `n`.

Here we prove the exact opposite, in the strongest possible form:

* `rule110_fixedSet` — for **every** ring size `n` (including `n = 0`, i.e. the
  bi-infinite configuration space `ℤ → 𝔽₂`), the fixed-point variety of Rule 110
  is the single point `0`.
* `rule110_hasFixedDim_zero` — hence Rule 110 has fixed-point dimension `0`,
  exactly like the null Rule 0.
* `rule110_not_hasFixedDim_max` — Rule 110 never attains the maximal dimension.
* `rule110_fixedSet_eq_rule0_fixedSet` and `fixed_variety_cannot_separate_rule110_rule0`
  — the fixed-point variety is *provably blind* to the difference between the
  Turing-complete Rule 110 and the constant Rule 0, so no invariant of `V(f)`
  whatsoever can recover Wolfram's classification.
* `rule110_globalUpdate_fixed_iff` — the Boolean, bi-infinite restatement in the
  language of `Novelty.CellularAutomataAlgebraicGeometry`, strengthening
  `rule110_constant_one_not_fixed` from that file to a complete classification.

The mechanism is a two-step *backward rigidity* argument: over `𝔽₂` the Rule 110
fixed-point equations read `s_{i+1} · (1 + s_i + s_{i-1} s_i) = 0`, so a cell
carrying a `1` forces its left neighbour to carry a `1` **and** its second-left
neighbour to carry a `0`, while the same constraint applied one step further to
the left forces that second-left neighbour to carry a `1`.  The contradiction is
local and uniform in `n`; no induction on the ring size is needed.
-/

open ECAFixedVariety

open CellularAutomataAlgebraicGeometry

theorem ECAFixedVariety.rule110_not_hasFixedDim_max(n : ℕ) (hn : 1 ≤ n) : ¬ HasFixedDim 110 n n := by sorry
