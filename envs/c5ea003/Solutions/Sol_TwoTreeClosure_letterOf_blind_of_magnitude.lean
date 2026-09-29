-- Prove2me | solution 1 for TwoTreeClosure.letterOf_blind_of_magnitude
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:38:53.446573+00:00
-- url     : https://prove2.me/submissions/72d08e5b-81f5-4ad2-a2e4-031d8fd1ed4e

-- Sol generated from Bridges/TwoTreeClosure/TreeCore.lean
import Mathlib
import Definitions.Def_Bridges_TwoTreeClosure_TreeCore

/-!
# The Berggren / Price tree of primitive Pythagorean triples: nodes, letters, blindness

This file develops the ternary Berggren tree in its Price coordinates: nodes are
pairs `(m, n)` with `m > n ≥ 1`, `gcd m n = 1` and `m + n` odd, the root is `(2,1)`,
and the three children of `(m, n)` are

* `A : (m, n) ↦ (2m - n, m)`,
* `B : (m, n) ↦ (2m + n, m)`,
* `C : (m, n) ↦ (m + 2n, n)`.

The triple attached to a node is `(m² - n², 2mn, m² + n²)`.

Main results.

* `isNode_childA/B/C`, `parent_*` : the tree is well defined and every non-root node
  has a unique parent, given by the *ascent letter* `letterOf`.
* `isNode.inTree` : **coverage** — every node in the arithmetic sense is reachable
  from the root `(2,1)`; the letter of a node is exactly the branch taken by its parent.
* `letterOf_blind_of_residue` : **residue dials are blind.**  For *every* modulus
  `M ≥ 1` and every scale `t ≥ 1` there are three nodes with hypotenuses all
  congruent to `1 mod M` and with the three distinct ascent letters.  Hence no
  function of `hyp mod M` computes the ascent letter (`residue_dial_letterBlind`),
  in particular no Gauss-sum style dial on `N mod 720720`.
* `letterOf_blind_of_magnitude` : **magnitude mirrors are blind.**  There is an
  infinite family of hypotenuses realised by two different nodes with *different*
  letters, e.g. `505 = 19² + 12² = 21² + 8² = 5 · 101`.  Hence no function of the
  hypotenuse itself — monotone or not — computes the ascent letter
  (`magnitude_probe_letterBlind`).
* `parityProfile_constant` : structural sensors (leg parities, Lorentz form) are
  *exactly* constant on the tree, so they are blind for trivial reasons.
-/

open TwoTreeClosure

/-! ### Nodes -/







/-! ### Children -/








/-! ### Ascent letters -/



theorem letterOf_eq_A {m n : ℕ} (h : m < 2 * n) : letterOf m n = Letter.A := by
  simp [letterOf, h]

theorem letterOf_eq_B {m n : ℕ} (h1 : 2 * n < m) (h2 : m < 3 * n) :
    letterOf m n = Letter.B := by
  simp [letterOf, h2]
  omega


/-! ### Reachability from the root, and coverage -/








/-! ### Blindness -/


/-! #### Strength 1–2: residue dials -/





/-! #### Strength 4: magnitude mirrors -/





/-! #### Strength 3: structurally constant sensors -/





/-! ### Branching base: the tree is exactly ternary

The ascent letter of a child names the branch that produced it, so the three
children of a node are pairwise distinct and each child remembers its parent.
Consequently the depth-`h` descendant set of any node has exactly `3 ^ h`
elements: the branching base of the Berggren/Price tree is pinned at `3`.
-/
















/-! ### The tree is free: injective child maps with disjoint ranges -/





open TwoTreeClosure in
theorem solution(t : ℕ) (ht : 1 ≤ t) :
    IsNode (20 * t - 1) (10 * t + 2) ∧ IsNode (20 * t + 1) (10 * t - 2) ∧
    hyp (20 * t - 1) (10 * t + 2) = hyp (20 * t + 1) (10 * t - 2) ∧
    letterOf (20 * t - 1) (10 * t + 2) = Letter.A ∧
    letterOf (20 * t + 1) (10 * t - 2) = Letter.B := by
  have hcop1 : Nat.Coprime (20 * t - 1) (10 * t + 2) := by
    have h1 : Nat.gcd (20 * t - 1) (10 * t + 2) ∣ 20 * t - 1 := Nat.gcd_dvd_left _ _
    have h2 : Nat.gcd (20 * t - 1) (10 * t + 2) ∣ 10 * t + 2 := Nat.gcd_dvd_right _ _
    have h3 : Nat.gcd (20 * t - 1) (10 * t + 2) ∣ 20 * t + 4 := by
      have := h2.mul_left 2
      simpa [show 2 * (10 * t + 2) = 20 * t + 4 from by ring] using this
    have h5 : Nat.gcd (20 * t - 1) (10 * t + 2) ∣ 5 := by
      have := Nat.dvd_sub h3 h1
      simpa [show 20 * t + 4 - (20 * t - 1) = 5 from by omega] using this
    -- a divisor of `5` dividing `20t - 1` must be `1`, since `5 ∤ 20t - 1`
    rcases (Nat.Prime.eq_one_or_self_of_dvd (by norm_num) _ h5) with h | h
    · exact h
    · exfalso
      rw [h] at h1
      omega
  have hcop2 : Nat.Coprime (20 * t + 1) (10 * t - 2) := by
    have h1 : Nat.gcd (20 * t + 1) (10 * t - 2) ∣ 20 * t + 1 := Nat.gcd_dvd_left _ _
    have h2 : Nat.gcd (20 * t + 1) (10 * t - 2) ∣ 10 * t - 2 := Nat.gcd_dvd_right _ _
    have h3 : Nat.gcd (20 * t + 1) (10 * t - 2) ∣ 20 * t - 4 := by
      have := h2.mul_left 2
      simpa [show 2 * (10 * t - 2) = 20 * t - 4 from by omega] using this
    have h5 : Nat.gcd (20 * t + 1) (10 * t - 2) ∣ 5 := by
      have := Nat.dvd_sub h1 h3
      simpa [show 20 * t + 1 - (20 * t - 4) = 5 from by omega] using this
    rcases (Nat.Prime.eq_one_or_self_of_dvd (by norm_num) _ h5) with h | h
    · exact h
    · exfalso
      rw [h] at h1
      omega
  refine ⟨⟨by omega, by omega, hcop1, by omega⟩, ⟨by omega, by omega, hcop2, by omega⟩, ?_,
    letterOf_eq_A (by omega), letterOf_eq_B (by omega) (by omega)⟩
  obtain ⟨s, hs⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  subst hs
  simp only [hyp]
  have e1 : 20 * (s + 1) - 1 = 20 * s + 19 := by omega
  have e2 : 10 * (s + 1) + 2 = 10 * s + 12 := by omega
  have e3 : 20 * (s + 1) + 1 = 20 * s + 21 := by omega
  have e4 : 10 * (s + 1) - 2 = 10 * s + 8 := by omega
  rw [e1, e2, e3, e4]
  ring
