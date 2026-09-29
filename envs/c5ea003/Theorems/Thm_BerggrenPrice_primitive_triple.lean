-- Prove2me | Theorems.Thm_BerggrenPrice_primitive_triple
-- name    : BerggrenPrice.primitive_triple
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:27:41.52941+00:00
-- url     : https://prove2.me/theorems/351d4a42-8034-429c-ba91-6b7a5292c43d
-- title:
--   Primitivity: the two legs at a node are coprime.
-- statement:
--   **Primitivity**: the two legs at a node are coprime.
--
--   ```lean
--   theorem BerggrenPrice.primitive_triple{v : Node} (h : IsNode v) : IsCoprime (oddLeg v) (evenLeg v) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/BerggrenPriceInterlock/NNode.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/BerggrenPriceInterlock/NNode.lean#L48

-- Thm stub generated from Algebra/BerggrenPriceInterlock/NNode.lean
import Mathlib
import Definitions.Def_Algebra_BerggrenPriceInterlock_Core
import Definitions.Def_Algebra_BerggrenPriceInterlock_NNode
import Definitions.Def_Algebra_BerggrenPriceInterlock_Trees

/-!
# Berggren–Price interlock, Part III: the N-node identity

A node `(m,n)` carries the primitive triple `(m² - n², 2mn, m² + n²)`.  The **odd leg**
factors as `(m-n)(m+n)`, so *a node is literally a factorisation*.  Conversely every odd
`N = p·q` with `p, q` coprime and `1 ≤ p < q` sits at the **Fermat pair**
`((p+q)/2, (q-p)/2)`, which is a valid node — hence a node of *both* trees, at a unique
address in each.

This makes the slogan "factoring `N` = finding the `N`-node" a theorem, and lets us
compare tree traversal with Fermat's own scan (`fermat_step_bound`: the number of trial
values is `m - r`, and `(m-r)(m+r) ≤ n² + 2r`, the classical `(q-p)²/(8√N)` law).

## Main results

* `pythagorean_triple`, `primitive_triple` — nodes give primitive Pythagorean triples.
* `fermatNode_eq`, `isNode_fermatNode`, `oddLeg_fermatNode` — the Fermat pair is a node
  and its odd leg is exactly `N = p·q`.
* `fermatNode_leftInverse`, `fermatNode_rightInverse`, `factorisation_of_node` — the
  correspondence `{coprime odd pairs} ≃ {nodes}` and extraction of a nontrivial divisor.
* `berg_N_node`, `price_N_node` — every such `N` is a node of *both* trees, at a unique
  address in each.
* `fermat_step_bound` — Fermat's scan length obeys `(m-r)(m+r) ≤ n² + 2r`.
-/

open BerggrenPrice

/-! ### The triple carried by a node -/

theorem BerggrenPrice.primitive_triple{v : Node} (h : IsNode v) : IsCoprime (oddLeg v) (evenLeg v) := by sorry
