-- Prove2me | solution 1 for ECAFixedVariety.rule110_fixedSet
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T22:11:54.063878+00:00
-- url     : https://prove2.me/submissions/d5fdb43c-c242-4b3b-94b9-d57a6fe77133

-- Sol generated from Novelty/ECAFixedVarietyRule110.lean
import Mathlib
import Definitions.Def_Novelty_ECAFixedVarietyCore
import Theorems.Thm_ECAFixedVariety_mem_fixedSet_iff
import Theorems.Thm_ECAFixedVariety_zmod2_eq_zero_or_one

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

/-- **Local rigidity of Rule 110.**  A neighbourhood is stationary for Rule 110
exactly when the right cell is `0`, or the centre is `1` and the left cell is `0`. -/
lemma rule110_local_iff :
    ∀ l c r : ZMod 2, localRuleZ 110 l c r = c ↔ (r = 0 ∨ (c = 1 ∧ l = 0)) := by decide








/-! ### Boolean bi-infinite restatement

We now transport the rigidity statement to the Boolean, bi-infinite setting of
`Novelty.CellularAutomataAlgebraicGeometry`, where it strengthens
`rule110_constant_one_not_fixed` to a complete description of the fixed set. -/




open ECAFixedVariety in
theorem solution(n : ℕ) : fixedSet 110 n = {0} := by
  ext s
  rw [mem_fixedSet_iff, Set.mem_singleton_iff]
  constructor
  · intro h
    funext i
    show s i = 0
    by_contra hne
    -- `s i = 1`, since we are over `𝔽₂`
    have hi : s i = 1 := (zmod2_eq_zero_or_one (s i)).resolve_left hne
    -- one step to the left: the `1` at `i` forces `s (i-1) = 1` and `s (i-2) = 0`
    have h1 := h (i - 1)
    rw [show i - 1 + 1 = i from by ring, rule110_local_iff] at h1
    have h1' : s (i - 1) = 1 ∧ s (i - 1 - 1) = 0 := by
      refine h1.resolve_left ?_
      rw [hi]
      decide
    -- two steps to the left: the `1` at `i-1` forces `s (i-2) = 1`
    have h2 := h (i - 1 - 1)
    rw [show i - 1 - 1 + 1 = i - 1 from by ring, rule110_local_iff] at h2
    have h2' : s (i - 1 - 1) = 1 ∧ s (i - 1 - 1 - 1) = 0 := by
      refine h2.resolve_left ?_
      rw [h1'.1]
      decide
    -- contradiction at the cell two steps to the left
    rw [h1'.2] at h2'
    exact absurd h2'.1 (by decide)
  · rintro rfl i
    simp [show localRuleZ 110 0 0 0 = 0 from by decide]
