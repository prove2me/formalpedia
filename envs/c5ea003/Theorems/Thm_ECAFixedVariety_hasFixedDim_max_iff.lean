-- Prove2me | Theorems.Thm_ECAFixedVariety_hasFixedDim_max_iff
-- name    : ECAFixedVariety.hasFixedDim_max_iff
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:31:47.974157+00:00
-- url     : https://prove2.me/theorems/25bbd3ea-4e1b-4ae3-ae65-afe6d416d298
-- title:
--   Maximal dimension characterises the identity automaton.
-- statement:
--   **Maximal dimension characterises the identity automaton.**
--
--   ```lean
--   theorem ECAFixedVariety.hasFixedDim_max_iff{rule n : ℕ} (hn : 3 ≤ n) :
--       HasFixedDim rule n n ↔ ∀ l c r : ZMod 2, localRuleZ rule l c r = c := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/ECAMaximalDimension.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/ECAMaximalDimension.lean#L112

-- Thm stub generated from Novelty/ECAMaximalDimension.lean
import Mathlib
import Definitions.Def_Novelty_ECAFixedVarietyCore
import Definitions.Def_Novelty_ECAPeriodicPointLattice

/-!
# Cycle 3: maximal dimension forces the identity automaton

The conjecture predicts that the Turing-complete class-4 rules have fixed-point
variety of maximal dimension `n`.  Cycles 1–2 showed Rule 110 has dimension `0`.
Here we close the question completely by classifying *which* elementary rules can
have a maximal-dimensional fixed-point variety: **exactly one, the identity Rule
204**, whose dynamics is trivial.

## Main results

* `exists_cfg_window` — on a ring of size `n ≥ 3` every `3`-cell window can be
  prescribed independently: the fixed-point equations really are `n` independent
  cubic equations.
* `fixedSet_eq_univ_iff` — the variety is all of `𝔸ⁿ` iff the local rule is the
  centre projection.
* `localRuleZ_eq_id_iff_eq_204` — for a genuine Wolfram number (`rule < 256`)
  that happens iff the rule is `204`.
* `hasFixedDim_max_iff` / `hasFixedDim_max_iff_eq_204` — **maximal dimension
  characterises the identity automaton**.  In particular the `255`
  non-identity rules, Rule 110 included, all fail the conjecture's class-4
  prediction, while the unique rule that satisfies it is the most trivial one in
  the whole family.
-/

open ECAFixedVariety

theorem ECAFixedVariety.hasFixedDim_max_iff{rule n : ℕ} (hn : 3 ≤ n) :
    HasFixedDim rule n n ↔ ∀ l c r : ZMod 2, localRuleZ rule l c r = c := by sorry
