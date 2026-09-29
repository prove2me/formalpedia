-- Prove2me | solution 1 for TwoTreeClosure.isNode_sgQ
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:38:52.877888+00:00
-- url     : https://prove2.me/submissions/96a81f50-02b8-41dd-aeb9-10ea1cfffb49

-- Sol generated from Bridges/TwoTreeClosure/RepresentationOrbit.lean
import Mathlib
import Definitions.Def_Bridges_TwoTreeClosure_RepresentationOrbit
import Definitions.Def_Bridges_TwoTreeClosure_TreeCore

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







open TwoTreeClosure in
theorem solution(s : ℕ) : IsNode (sgQ s).1 (sgQ s).2 := by
  refine ⟨by norm_num [sgQ], ?_, ?_, ?_⟩
  · simp only [sgQ]
    nlinarith [Nat.zero_le (s ^ 2), Nat.zero_le s]
  · show Nat.gcd (4 * s ^ 2 + 28 * s + 49) 2 = 1
    obtain ⟨g, hg⟩ : ∃ g, Nat.gcd (4 * s ^ 2 + 28 * s + 49) 2 = g := ⟨_, rfl⟩
    have hdP : g ∣ 4 * s ^ 2 + 28 * s + 49 := hg ▸ Nat.gcd_dvd_left _ _
    have hd2 : g ∣ 2 := hg ▸ Nat.gcd_dvd_right _ _
    have hle : g ≤ 2 := Nat.le_of_dvd (by norm_num) hd2
    rw [hg]
    obtain ⟨k, hk⟩ := hdP
    interval_cases g
    · omega
    · rfl
    · omega
  · simp only [sgQ]
    omega
