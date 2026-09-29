-- Prove2me | solution 1 for ECAFixedVariety.hasFixedDim_max_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T21:57:25.410298+00:00
-- url     : https://prove2.me/submissions/8bb95fe3-6986-4d27-8168-abafa20b00f6

-- Sol generated from Novelty/ECAMaximalDimension.lean
import Mathlib
import Definitions.Def_Novelty_ECAFixedVarietyCore
import Definitions.Def_Novelty_ECAPeriodicPointLattice
import Theorems.Thm_ECAFixedVariety_fixedSet_eq_univ_iff

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
theorem solution{rule n : ℕ} (hn : 3 ≤ n) :
    HasFixedDim rule n n ↔ ∀ l c r : ZMod 2, localRuleZ rule l c r = c := by
  haveI : NeZero n := ⟨by omega⟩
  constructor
  · intro h
    obtain ⟨W, hW, hd⟩ := h
    have hdim : Module.finrank (ZMod 2) (Cfg n) = n := by simp [Cfg]
    have htop : W = ⊤ := Submodule.eq_top_of_finrank_eq (by rw [hd, hdim])
    rw [htop] at hW
    have : fixedSet rule n = Set.univ := by
      rw [← hW]
      simp
    exact (fixedSet_eq_univ_iff hn).1 this
  · intro h
    have huniv : fixedSet rule n = Set.univ := (fixedSet_eq_univ_iff hn).2 h
    refine ⟨⊤, by simp [huniv], ?_⟩
    rw [finrank_top]
    simp [Cfg]
