-- Prove2me | solution 1 for TwoTreeClosure.letterOf_blind_of_residue
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:44:11.765402+00:00
-- url     : https://prove2.me/submissions/dae1d671-21a0-4e19-b5d8-b997b2a88510

-- Sol generated from Bridges/TwoTreeClosure/TreeCore.lean
import Mathlib
import Definitions.Def_Bridges_TwoTreeClosure_TreeCore
import Theorems.Thm_TwoTreeClosure_letterOf_eq_C

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
theorem solution(M n : ℕ) (hn2 : 2 ≤ n) (hne : n % 2 = 0)
    (hMn : M ∣ n) :
    letterOf (n + 1) n = Letter.A ∧
    letterOf (2 * n + 1) n = Letter.B ∧
    letterOf (3 * n + 1) n = Letter.C ∧
    IsNode (n + 1) n ∧ IsNode (2 * n + 1) n ∧ IsNode (3 * n + 1) n ∧
    hyp (n + 1) n % M = 1 % M ∧
    hyp (2 * n + 1) n % M = 1 % M ∧
    hyp (3 * n + 1) n % M = 1 % M := by
  have hcop1 : Nat.Coprime (n + 1) n := by simp
  have hcop2 : Nat.Coprime (2 * n + 1) n := by simp
  have hcop3 : Nat.Coprime (3 * n + 1) n := by simp
  obtain ⟨c, hc⟩ := hMn
  refine ⟨letterOf_eq_A (by omega), letterOf_eq_B (by omega) (by omega),
    letterOf_eq_C (by omega), ⟨by omega, by omega, hcop1, by omega⟩,
    ⟨by omega, by omega, hcop2, by omega⟩, ⟨by omega, by omega, hcop3, by omega⟩, ?_, ?_, ?_⟩
  · have e : hyp (n + 1) n = 1 + M * (M * (2 * c ^ 2) + 2 * c) := by
      simp only [hyp, hc]; ring
    rw [e, Nat.add_mul_mod_self_left]
  · have e : hyp (2 * n + 1) n = 1 + M * (M * (5 * c ^ 2) + 4 * c) := by
      simp only [hyp, hc]; ring
    rw [e, Nat.add_mul_mod_self_left]
  · have e : hyp (3 * n + 1) n = 1 + M * (M * (10 * c ^ 2) + 6 * c) := by
      simp only [hyp, hc]; ring
    rw [e, Nat.add_mul_mod_self_left]
