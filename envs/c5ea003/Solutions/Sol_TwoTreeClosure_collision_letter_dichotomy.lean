-- Prove2me | solution 1 for TwoTreeClosure.collision_letter_dichotomy
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:41:16.793512+00:00
-- url     : https://prove2.me/submissions/c4ebf430-d10a-4b25-974b-03b37cb50133

-- Sol generated from Bridges/TwoTreeClosure/RepresentationOrbit.lean
import Mathlib
import Definitions.Def_Bridges_TwoTreeClosure_RepresentationOrbit
import Definitions.Def_Bridges_TwoTreeClosure_TreeCore
import Theorems.Thm_TwoTreeClosure_hyp_sgP
import Theorems.Thm_TwoTreeClosure_hyp_sgQ
import Theorems.Thm_TwoTreeClosure_isNode_sgP
import Theorems.Thm_TwoTreeClosure_isNode_sgQ
import Theorems.Thm_TwoTreeClosure_letterOf_blind_of_magnitude
import Theorems.Thm_TwoTreeClosure_letterOf_sgP
import Theorems.Thm_TwoTreeClosure_letterOf_sgQ
import Theorems.Thm_TwoTreeClosure_sgP_ne_sgQ

/-!
# Magnitude collisions need not split the ascent letter — the orbit conjecture is false

`Bridges.TwoTreeClosure.TreeCore` proves *magnitude blindness* by exhibiting a family
of hypotenuse collisions whose two nodes carry **different** ascent letters
(`letterOf_blind_of_magnitude`).  The natural strengthening — proposed as direction 1
of the previous cycle's `FUTURE_DIRECTIONS.md` — was the *orbit conjecture*:

> whenever `N` has two essentially distinct primitive representations as a sum of two
> coprime squares, the two corresponding tree nodes carry **different** ascent letters,

which would have turned magnitude blindness into a structure theorem and, read the
other way round, would have given a genuine one-bit signal ("the letters of a
collision are never equal").

This file **refutes** that conjecture with an explicit infinite family coming from the
Sophie Germain identity `u⁴ + 4 = (u² - 2u + 2)(u² + 2u + 2)`.  Writing `u = 2s + 7`,

* `sgN s = (4s² + 28s + 49)² + 4 = (4s² + 24s + 37)(4s² + 32s + 65)` is composite;
* it is the hypotenuse of the two distinct primitive nodes
  `sgP s = (4s² + 28s + 47, 4s + 14)` (the `(u² - 2, 2u)` representation) and
  `sgQ s = (4s² + 28s + 49, 2)` (the `(u², 2)` representation);
* and **both** nodes have ascent letter `C`, because `u² - 2 > 3 · 2u` for `u ≥ 7`.

Consequences.

* `orbit_letter_separation_false` : the orbit conjecture is false.
* `collision_letter_dichotomy` : *both* phenomena occur above every bound — there are
  hypotenuse collisions with equal letters and hypotenuse collisions with distinct
  letters.  So "does `N` admit a collision?" carries no letter information at all: the
  letter multiset of the representations of `N` is not a function of the collision
  pattern, and the residual positional content of the tree is not addressable by
  counting representations.

The smallest member (`s = 0`) is `2405 = 5 · 13 · 37 = 47² + 14² = 49² + 2²`, with
`47 > 3 · 14` and `49 > 3 · 2`: two `C`'s.
-/

open TwoTreeClosure

/-! ### The Sophie Germain collision family -/








/-! ### Both members are genuine primitive nodes -/




/-! ### Both members carry the same ascent letter -/




/-! ### The refutation -/




/-- The family is unbounded: `sgN s ≥ s`, so same-letter collisions occur at every
scale. -/
theorem sgN_ge (s : ℕ) : s ≤ sgN s := by
  simp only [sgN]
  nlinarith [Nat.zero_le (s ^ 2), Nat.zero_le s]



open TwoTreeClosure in
theorem solution(T : ℕ) :
    (∃ m n m' n' : ℕ, T ≤ hyp m n ∧ IsNode m n ∧ IsNode m' n' ∧ hyp m n = hyp m' n' ∧
        (m, n) ≠ (m', n') ∧ letterOf m n = letterOf m' n') ∧
    (∃ m n m' n' : ℕ, T ≤ hyp m n ∧ IsNode m n ∧ IsNode m' n' ∧ hyp m n = hyp m' n' ∧
        (m, n) ≠ (m', n') ∧ letterOf m n ≠ letterOf m' n') := by
  constructor
  · refine ⟨(sgP T).1, (sgP T).2, (sgQ T).1, (sgQ T).2, ?_, isNode_sgP T, isNode_sgQ T,
      by rw [hyp_sgP, hyp_sgQ], by simpa using sgP_ne_sgQ T, ?_⟩
    · rw [hyp_sgP]; exact sgN_ge T
    · rw [letterOf_sgP, letterOf_sgQ]
  · obtain ⟨hnA, hnB, hhyp, hA, hB⟩ := letterOf_blind_of_magnitude (T + 1) (by omega)
    refine ⟨20 * (T + 1) - 1, 10 * (T + 1) + 2, 20 * (T + 1) + 1, 10 * (T + 1) - 2,
      ?_, hnA, hnB, hhyp, ?_, ?_⟩
    · simp only [hyp]
      have e : 20 * (T + 1) - 1 = 20 * T + 19 := by omega
      rw [e]
      nlinarith [Nat.zero_le (T ^ 2), Nat.zero_le T]
    · intro h
      have h1 : (20 * (T + 1) - 1 : ℕ) = 20 * (T + 1) + 1 := congrArg Prod.fst h
      omega
    · rw [hA, hB]
      exact Letter.noConfusion
