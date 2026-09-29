-- Prove2me | Definitions.Def_Algebra_BerggrenPriceInterlock_NNode
-- name    : Algebra_BerggrenPriceInterlock_NNode
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T08:08:30.649291+00:00
-- url     : https://prove2.me/theorems/2f25ec8a-a311-48ce-bfe2-30cb2ce4ab81
-- title:
--   Aether Catalog definitions — Algebra_BerggrenPriceInterlock_NNode
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.BerggrenPriceInterlock.NNode`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/BerggrenPriceInterlock/NNode.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Algebra_BerggrenPriceInterlock_Core
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

namespace BerggrenPrice

/-! ### The triple carried by a node -/

/-- The odd leg `m² - n²` of the triple at a node. -/
def oddLeg (v : Node) : ℤ := v.1 ^ 2 - v.2 ^ 2
/-- The even leg `2mn` of the triple at a node. -/
def evenLeg (v : Node) : ℤ := 2 * v.1 * v.2
/-- The hypotenuse `m² + n²` of the triple at a node. -/
def hypot (v : Node) : ℤ := v.1 ^ 2 + v.2 ^ 2




/-! ### The Fermat pair of a factorisation -/

/-- The **Fermat pair** of the factorisation `N = p·q`: `((p+q)/2, (q-p)/2)`. -/
def fermatNode (p q : ℤ) : Node := ((p + q) / 2, (q - p) / 2)


variable {p q : ℤ}








/-! ### The N-node lives in both trees -/





/-! ### Fermat's own scan -/



end BerggrenPrice


