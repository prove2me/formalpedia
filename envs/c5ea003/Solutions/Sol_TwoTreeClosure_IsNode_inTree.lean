-- Prove2me | solution 1 for TwoTreeClosure.IsNode.inTree
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:15:10.725165+00:00
-- url     : https://prove2.me/submissions/06b02ac4-f6a6-46a1-b32d-9f0f6f5b2041

-- Sol generated from Bridges/TwoTreeClosure/TreeCore.lean
import Mathlib
import Definitions.Def_Bridges_TwoTreeClosure_TreeCore
import Theorems.Thm_TwoTreeClosure_isNode_parentA
import Theorems.Thm_TwoTreeClosure_isNode_parentB
import Theorems.Thm_TwoTreeClosure_node_ratio_trichotomy

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






/-! ### Reachability from the root, and coverage -/





/-- Parent of a `C`-node is a node. -/
theorem isNode_parentC {m n : ℕ} (h : IsNode m n) (h1 : 3 * n < m) :
    IsNode (m - 2 * n) n := by
  obtain ⟨hn, hnm, hcop, hpar⟩ := h
  refine ⟨by omega, by omega, ?_, by omega⟩
  have h1' : Nat.gcd (m - 2 * n) n ∣ (m - 2 * n) := Nat.gcd_dvd_left _ _
  have h2' : Nat.gcd (m - 2 * n) n ∣ n := Nat.gcd_dvd_right _ _
  have h3' : Nat.gcd (m - 2 * n) n ∣ 2 * n := h2'.mul_left 2
  have h4' : Nat.gcd (m - 2 * n) n ∣ m := by
    have := Nat.dvd_add h1' h3'
    simpa [show m - 2 * n + 2 * n = m from by omega] using this
  have h5' : Nat.gcd (m - 2 * n) n ∣ Nat.gcd m n := Nat.dvd_gcd h4' h2'
  exact Nat.eq_one_of_dvd_one (hcop ▸ h5')



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
theorem solution: ∀ m : ℕ, ∀ n : ℕ, IsNode m n → InTree m n := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro n h
    by_cases hroot : m = 2 ∧ n = 1
    · obtain ⟨rfl, rfl⟩ := hroot
      exact InTree.root
    · rcases node_ratio_trichotomy h hroot with ⟨h1, h2⟩ | ⟨h1, h2⟩ | h1
      · have hp := isNode_parentA h h1 h2
        have hlt : n < m := h1
        have := (ih n hlt (2 * n - m) hp).stepA
        rwa [show 2 * n - (2 * n - m) = m from by omega] at this
      · have hp := isNode_parentB h h1 h2
        have hlt : n < m := by omega
        have := (ih n hlt (m - 2 * n) hp).stepB
        rwa [show 2 * n + (m - 2 * n) = m from by omega] at this
      · have hp := isNode_parentC h h1
        have hn : 1 ≤ n := h.1
        have hlt : m - 2 * n < m := by omega
        have := (ih (m - 2 * n) hlt n hp).stepC
        rwa [show m - 2 * n + 2 * n = m from by omega] at this
