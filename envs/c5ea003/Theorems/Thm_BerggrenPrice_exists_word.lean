-- Prove2me | Theorems.Thm_BerggrenPrice_exists_word
-- name    : BerggrenPrice.exists_word
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:26:34.400426+00:00
-- url     : https://prove2.me/theorems/49e916de-eb8e-464f-a549-07542987f69f
-- title:
--   Descent / completeness.
-- statement:
--   **Descent / completeness.**  Every node is reached from the root by some word.
--
--   ```lean
--   theorem BerggrenPrice.exists_word: ∀ (v : Node), IsNode v → ∃ w : List (Fin 3), applyWord f w root = v := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/BerggrenPriceInterlock/Core.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/BerggrenPriceInterlock/Core.lean#L89

-- Thm stub generated from Algebra/BerggrenPriceInterlock/Core.lean
import Mathlib
import Definitions.Def_Algebra_BerggrenPriceInterlock_Core

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

include hsize hparent in

theorem BerggrenPrice.exists_word: ∀ (v : Node), IsNode v → ∃ w : List (Fin 3), applyWord f w root = v := by sorry
