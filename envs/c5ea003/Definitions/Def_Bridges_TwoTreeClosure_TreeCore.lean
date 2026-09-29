-- Prove2me | Definitions.Def_Bridges_TwoTreeClosure_TreeCore
-- name    : Bridges_TwoTreeClosure_TreeCore
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:44:25.631028+00:00
-- url     : https://prove2.me/theorems/cd8b1bde-5668-49b1-b7b6-a5182af205ec
-- title:
--   Aether Catalog definitions — Bridges_TwoTreeClosure_TreeCore
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.TwoTreeClosure.TreeCore`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/TwoTreeClosure/TreeCore.lean by skeleton subtraction
import Mathlib

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

namespace TwoTreeClosure

/-! ### Nodes -/

/-- A Price/Berggren node: `m > n ≥ 1`, coprime, of opposite parity. -/
def IsNode (m n : ℕ) : Prop :=
  1 ≤ n ∧ n < m ∧ Nat.Coprime m n ∧ (m + n) % 2 = 1

/-- The hypotenuse attached to a node. -/
def hyp (m n : ℕ) : ℕ := m ^ 2 + n ^ 2

/-- The odd leg attached to a node. -/
def legOdd (m n : ℕ) : ℕ := m ^ 2 - n ^ 2

/-- The even leg attached to a node. -/
def legEven (m n : ℕ) : ℕ := 2 * m * n



/-! ### Children -/

/-- Berggren/Price child `A`. -/
def childA (m n : ℕ) : ℕ × ℕ := (2 * m - n, m)
/-- Berggren/Price child `B`. -/
def childB (m n : ℕ) : ℕ × ℕ := (2 * m + n, m)
/-- Berggren/Price child `C`. -/
def childC (m n : ℕ) : ℕ × ℕ := (m + 2 * n, n)







/-! ### Ascent letters -/

/-- The three branch letters. -/
inductive Letter | A | B | C
  deriving DecidableEq, Repr

/-- The ascent letter of a node: which of the three branches produced it.  It is a
pure ratio test: `A` for `n < m < 2n`, `B` for `2n < m < 3n`, `C` for `m > 3n`. -/
def letterOf (m n : ℕ) : Letter :=
  if m < 2 * n then Letter.A else if m < 3 * n then Letter.B else Letter.C




/-! ### Reachability from the root, and coverage -/

/-- Reachability in the Berggren/Price tree from the root `(2,1)`. -/
inductive InTree : ℕ → ℕ → Prop
  | root : InTree 2 1
  | stepA {m n : ℕ} : InTree m n → InTree (2 * m - n) m
  | stepB {m n : ℕ} : InTree m n → InTree (2 * m + n) m
  | stepC {m n : ℕ} : InTree m n → InTree (m + 2 * n) n







/-! ### Blindness -/

/-- A sensor `s` on nodes is *letter blind* if it takes the same value at two nodes
carrying different ascent letters: no decision rule based on `s` can output the
letter. -/
def LetterBlind {β : Type} (s : ℕ → ℕ → β) : Prop :=
  ∃ m n m' n', IsNode m n ∧ IsNode m' n' ∧ s m n = s m' n' ∧ letterOf m n ≠ letterOf m' n'

/-! #### Strength 1–2: residue dials -/





/-! #### Strength 4: magnitude mirrors -/





/-! #### Strength 3: structurally constant sensors -/

/-- The parity profile of the Euclid triple of a node. -/
def parityProfile (m n : ℕ) : ℕ × ℕ × ℕ := (legOdd m n % 2, legEven m n % 2, hyp m n % 2)




/-! ### Branching base: the tree is exactly ternary

The ascent letter of a child names the branch that produced it, so the three
children of a node are pairwise distinct and each child remembers its parent.
Consequently the depth-`h` descendant set of any node has exactly `3 ^ h`
elements: the branching base of the Berggren/Price tree is pinned at `3`.
-/

/-- The parent map, driven by the ascent letter. -/
def parentP (p : ℕ × ℕ) : ℕ × ℕ :=
  match letterOf p.1 p.2 with
  | Letter.A => (p.2, 2 * p.2 - p.1)
  | Letter.B => (p.2, p.1 - 2 * p.2)
  | Letter.C => (p.1 - 2 * p.2, p.2)







/-- The set of children of a node. -/
def childrenF (p : ℕ × ℕ) : Finset (ℕ × ℕ) :=
  {childA p.1 p.2, childB p.1 p.2, childC p.1 p.2}




/-- Depth-`h` descendants of a node. -/
def desc (p : ℕ × ℕ) : ℕ → Finset (ℕ × ℕ)
  | 0 => {p}
  | h + 1 => (desc p h).biUnion childrenF




/-! ### The tree is free: injective child maps with disjoint ranges -/




end TwoTreeClosure


