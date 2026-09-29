-- Prove2me | Definitions.Def_Algebra_BerggrenPriceInterlock_Core
-- name    : Algebra_BerggrenPriceInterlock_Core
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T08:05:52.657031+00:00
-- url     : https://prove2.me/theorems/19dd5554-7c50-4869-9092-e5fa86812c62
-- title:
--   Aether Catalog definitions — Algebra_BerggrenPriceInterlock_Core
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.BerggrenPriceInterlock.Core`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/BerggrenPriceInterlock/Core.lean by skeleton subtraction
import Mathlib

/-!
# Berggren–Price interlock, Part I: an abstract ternary descent framework

Both classical trees of primitive Pythagorean triples (Barning–Hall–Berggren and Price)
become, in the *Euclid parameter* coordinates `(m, n)`, ternary trees on the set

  `Node = {(m,n) : 1 ≤ n < m, gcd(m,n) = 1, m + n odd}`

rooted at `(2,1)`.  This file isolates the purely combinatorial content that makes such a
family of three maps a *tree*: every node is `applyWord w root` for a **unique** word `w`.

The five hypotheses are: the maps preserve nodes, strictly increase the size `m + n`,
are injective, have pairwise disjoint images on nodes, and every non-root node has a
parent.  Both concrete trees are shown to satisfy them in
`Algebra.BerggrenPriceInterlock.Trees`.

## Main results

* `IsNode.size_ge` — every node has size `≥ 3`, with equality only at the root.
* `exists_word` — existence of a root-to-node word (Fermat descent).
* `word_unique` — uniqueness of that word (disjointness of the three subtrees).
* `exists_unique_word` — the two combined: the tree is a bijection `words ≃ nodes`.
-/

namespace BerggrenPrice

/-- A node of either Pythagorean tree, in Euclid parameters `(m, n)`. -/
abbrev Node := ℤ × ℤ

/-- Valid Euclid parameters: `1 ≤ n < m`, coprime, of opposite parity. -/
def IsNode (v : Node) : Prop :=
  1 ≤ v.2 ∧ v.2 < v.1 ∧ IsCoprime v.1 v.2 ∧ Odd (v.1 + v.2)

/-- The root `(2,1)` of both trees, i.e. the triple `(3,4,5)`. -/
def root : Node := (2, 1)

/-- The size of a node, the quantity that strictly increases along every tree edge. -/
def size (v : Node) : ℤ := v.1 + v.2





section Abstract

variable (f : Fin 3 → Node → Node)

/-- Apply a word of tree letters, the head letter acting **last** (outermost). -/
def applyWord : List (Fin 3) → Node → Node
  | [], v => v
  | i :: w, v => f i (applyWord w v)



variable (hmap : ∀ i v, IsNode v → IsNode (f i v))


variable (hsize : ∀ i v, IsNode v → size v < size (f i v))
variable (hparent : ∀ v, IsNode v → v ≠ root → ∃ i u, IsNode u ∧ f i u = v)


variable (hinj : ∀ i u v, f i u = f i v → u = v)
variable (hdisj : ∀ i j u v, IsNode u → IsNode v → f i u = f j v → i = j)



end Abstract

end BerggrenPrice


