-- Prove2me | Theorems.Thm_BerggrenPrice_isNode_root
-- name    : BerggrenPrice.isNode_root
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:26:37.920456+00:00
-- url     : https://prove2.me/theorems/18d68727-df5d-4238-8042-c4d99037f248
-- title:
--   IsNode root
-- statement:
--   Formal statement of `BerggrenPrice.isNode_root` from the Aether Catalog (Algebra). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem BerggrenPrice.isNode_root: IsNode root := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/BerggrenPriceInterlock/Core.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/BerggrenPriceInterlock/Core.lean#L41

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

theorem BerggrenPrice.isNode_root: IsNode root := by sorry
