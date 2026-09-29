-- Prove2me | solution 1 for BerggrenPrice.exists_unique_word
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T14:06:08.257989+00:00
-- url     : https://prove2.me/submissions/03278615-8ae7-4808-8769-98020788db39

-- Sol generated from Algebra/BerggrenPriceInterlock/Core.lean
import Mathlib
import Definitions.Def_Algebra_BerggrenPriceInterlock_Core
import Theorems.Thm_BerggrenPrice_exists_word
import Theorems.Thm_BerggrenPrice_word_unique

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

open BerggrenPrice










variable (f : Fin 3 → Node → Node)




variable (hmap : ∀ i v, IsNode v → IsNode (f i v))


variable (hsize : ∀ i v, IsNode v → size v < size (f i v))
variable (hparent : ∀ v, IsNode v → v ≠ root → ∃ i u, IsNode u ∧ f i u = v)


variable (hinj : ∀ i u v, f i u = f i v → u = v)
variable (hdisj : ∀ i j u v, IsNode u → IsNode v → f i u = f j v → i = j)





open BerggrenPrice in
include hmap hsize hinj hdisj hparent in
theorem solution(v : Node) (hv : IsNode v) :
    ∃! w : List (Fin 3), applyWord f w root = v := by
  obtain ⟨w, hw⟩ := exists_word f hsize hparent v hv
  exact ⟨w, hw, fun w' hw' => word_unique f hmap hsize hinj hdisj w' w (by rw [hw, hw'])⟩
