-- Prove2me | solution 1 for TwoTreeClosure.residue_dial_letterBlind
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:45:40.131693+00:00
-- url     : https://prove2.me/submissions/515f9347-99f3-4c55-8531-fed342c20284

-- Sol generated from Bridges/TwoTreeClosure/TreeCore.lean
import Mathlib
import Definitions.Def_Bridges_TwoTreeClosure_TreeCore
import Theorems.Thm_TwoTreeClosure_letterOf_blind_of_residue

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


/-- For every modulus there is such a scale: `n = 2 * M * t`. -/
theorem residue_scale_exists (M t : ℕ) (hM : 1 ≤ M) (ht : 1 ≤ t) :
    2 ≤ 2 * M * t ∧ (2 * M * t) % 2 = 0 ∧ M ∣ 2 * M * t := by
  have hfac : 2 * M * t = 2 * (M * t) := by ring
  have hpos : 1 ≤ M * t := Nat.one_le_iff_ne_zero.2 (by positivity)
  exact ⟨by omega, by omega, ⟨2 * t, by ring⟩⟩



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
theorem solution(M : ℕ) (hM : 1 ≤ M) (g : ℕ → Letter) :
    ¬ (∀ m n, IsNode m n → g (hyp m n % M) = letterOf m n) := by
  intro hg
  obtain ⟨hs2, hse, hsd⟩ := residue_scale_exists M 1 hM le_rfl
  obtain ⟨hA, hB, -, hnA, hnB, -, hrA, hrB, -⟩ :=
    letterOf_blind_of_residue M (2 * M * 1) hs2 hse hsd
  have e1 := hg _ _ hnA
  have e2 := hg _ _ hnB
  rw [hA] at e1
  rw [hB] at e2
  rw [hrA] at e1
  rw [hrB] at e2
  rw [e1] at e2
  exact Letter.noConfusion e2
