-- Prove2me | solution 1 for TwoTreeClosure.isNode_childA
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:16:56.830603+00:00
-- url     : https://prove2.me/submissions/2725890a-54f3-4b81-9728-18ef47ea206c

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


private lemma coprime_two_mul_sub {m n : ℕ} (h : Nat.Coprime m n) (hle : n ≤ 2 * m) :
    Nat.Coprime (2 * m - n) m := by
  have h1 : Nat.gcd (2 * m - n) m ∣ 2 * m - n := Nat.gcd_dvd_left _ _
  have h2 : Nat.gcd (2 * m - n) m ∣ m := Nat.gcd_dvd_right _ _
  have h3 : Nat.gcd (2 * m - n) m ∣ 2 * m := h2.mul_left 2
  have h4 : Nat.gcd (2 * m - n) m ∣ n := by
    have := Nat.dvd_sub h3 h1
    simpa [show 2 * m - (2 * m - n) = n from by omega] using this
  have h5 : Nat.gcd (2 * m - n) m ∣ Nat.gcd m n := Nat.dvd_gcd h2 h4
  exact Nat.eq_one_of_dvd_one (h ▸ h5)






/-! ### Ascent letters -/






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
theorem solution{m n : ℕ} (h : IsNode m n) : IsNode (2 * m - n) m := by
  obtain ⟨hn, hnm, hcop, hpar⟩ := h
  exact ⟨by omega, by omega, coprime_two_mul_sub hcop (by omega), by omega⟩
