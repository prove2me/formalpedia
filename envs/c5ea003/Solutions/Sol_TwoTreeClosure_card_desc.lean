-- Prove2me | solution 1 for TwoTreeClosure.card_desc
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:36:50.706107+00:00
-- url     : https://prove2.me/submissions/67e9b25b-1dfc-41c5-b86b-bdf3577251b1

-- Sol generated from Bridges/TwoTreeClosure/TreeCore.lean
import Mathlib
import Definitions.Def_Bridges_TwoTreeClosure_TreeCore
import Theorems.Thm_TwoTreeClosure_card_childrenF
import Theorems.Thm_TwoTreeClosure_desc_isNode
import Theorems.Thm_TwoTreeClosure_parentP_childA
import Theorems.Thm_TwoTreeClosure_parentP_childB
import Theorems.Thm_TwoTreeClosure_parentP_childC

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











theorem parentP_of_mem_children {m n : ℕ} (h : IsNode m n) :
    ∀ p ∈ childrenF (m, n), parentP p = (m, n) := by
  intro p hp
  simp only [childrenF, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl
  · exact parentP_childA h
  · exact parentP_childB h
  · exact parentP_childC h





/-! ### The tree is free: injective child maps with disjoint ranges -/





open TwoTreeClosure in
theorem solution{m n : ℕ} (h : IsNode m n) : ∀ k : ℕ, (desc (m, n) k).card = 3 ^ k := by
  intro k
  induction k with
  | zero => simp [desc]
  | succ k ih =>
      have hdisj : ∀ x ∈ desc (m, n) k, ∀ y ∈ desc (m, n) k, x ≠ y →
          Disjoint (childrenF x) (childrenF y) := by
        intro x hx y hy hxy
        have hxn : IsNode x.1 x.2 := desc_isNode h k x hx
        have hyn : IsNode y.1 y.2 := desc_isNode h k y hy
        rw [Finset.disjoint_left]
        intro a hax hay
        have h1 : parentP a = x := by
          have : childrenF x = childrenF (x.1, x.2) := by simp
          rw [this] at hax
          simpa using parentP_of_mem_children hxn a hax
        have h2 : parentP a = y := by
          have : childrenF y = childrenF (y.1, y.2) := by simp
          rw [this] at hay
          simpa using parentP_of_mem_children hyn a hay
        exact hxy (h1 ▸ h2 ▸ rfl)
      have hcard : ∀ x ∈ desc (m, n) k, (childrenF x).card = 3 := by
        intro x hx
        have hxn : IsNode x.1 x.2 := desc_isNode h k x hx
        have : childrenF x = childrenF (x.1, x.2) := by simp
        rw [this]
        exact card_childrenF hxn
      calc (desc (m, n) (k + 1)).card
          = ∑ x ∈ desc (m, n) k, (childrenF x).card := by
            simp only [desc]
            exact Finset.card_biUnion hdisj
        _ = ∑ _x ∈ desc (m, n) k, 3 := Finset.sum_congr rfl hcard
        _ = 3 ^ k * 3 := by rw [Finset.sum_const, ih]; ring
        _ = 3 ^ (k + 1) := by ring
