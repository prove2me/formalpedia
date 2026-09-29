-- Prove2me | solution 1 for ECAFixedVariety.rule110_globalUpdate_fixed_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T22:13:24.126165+00:00
-- url     : https://prove2.me/submissions/7e2f2efa-b49e-4363-a99c-19accd2eb6b3

-- Sol generated from Novelty/ECAFixedVarietyRule110.lean
import Mathlib
import Definitions.Def_Novelty_CellularAutomataAlgebraicGeometry
import Definitions.Def_Novelty_ECAFixedVarietyCore
import Theorems.Thm_CellularAutomataAlgebraicGeometry_rule110_constant_zero_fixed

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









/-! ### Boolean bi-infinite restatement

We now transport the rigidity statement to the Boolean, bi-infinite setting of
`Novelty.CellularAutomataAlgebraicGeometry`, where it strengthens
`rule110_constant_one_not_fixed` to a complete description of the fixed set. -/

/-- Local rigidity of Rule 110, Boolean form. -/
lemma rule110_localRule_iff :
    ∀ l c r : Bool, localRule 110 l c r = c ↔ (r = false ∨ (c = true ∧ l = false)) := by decide



open ECAFixedVariety in
theorem solution(state : Int → Bool) :
    globalUpdate 110 state = state ↔ state = fun _ => false := by
  constructor
  · intro h
    funext i
    by_contra hne
    have hi : state i = true := by
      cases hst : state i with
      | false => exact absurd hst hne
      | true => rfl
    have h1 := congrFun h (i - 1)
    simp only [globalUpdate, show i - 1 + 1 = i from by ring] at h1
    rw [rule110_localRule_iff] at h1
    have h1' : state (i - 1) = true ∧ state (i - 1 - 1) = false := by
      refine h1.resolve_left ?_
      rw [hi]
      exact Bool.noConfusion
    have h2 := congrFun h (i - 1 - 1)
    simp only [globalUpdate, show i - 1 - 1 + 1 = i - 1 from by ring] at h2
    rw [rule110_localRule_iff] at h2
    have h2' : state (i - 1 - 1) = true ∧ state (i - 1 - 1 - 1) = false := by
      refine h2.resolve_left ?_
      rw [h1'.1]
      exact Bool.noConfusion
    rw [h1'.2] at h2'
    exact Bool.noConfusion h2'.1
  · rintro rfl
    exact rule110_constant_zero_fixed
