-- Prove2me | solution 1 for ECAFixedVariety.hasFixedDim_max_iff_eq_204
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T22:05:27.164782+00:00
-- url     : https://prove2.me/submissions/81afff79-d715-48cb-b410-52dceca9f873

-- Sol generated from Novelty/ECAMaximalDimension.lean
import Mathlib
import Definitions.Def_Novelty_ECAFixedVarietyCore
import Definitions.Def_Novelty_ECAPeriodicPointLattice
import Theorems.Thm_ECAFixedVariety_hasFixedDim_max_iff
import Theorems.Thm_ECAFixedVariety_localRuleZ_eq_id_iff_eq_204

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









open ECAFixedVariety in
theorem solution{rule n : ℕ} (hrule : rule < 256) (hn : 3 ≤ n) :
    HasFixedDim rule n n ↔ rule = 204 :=
  (hasFixedDim_max_iff hn).trans (localRuleZ_eq_id_iff_eq_204 hrule)
