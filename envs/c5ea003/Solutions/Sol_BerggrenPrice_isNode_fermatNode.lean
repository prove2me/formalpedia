-- Prove2me | solution 1 for BerggrenPrice.isNode_fermatNode
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T11:45:26.617964+00:00
-- url     : https://prove2.me/submissions/4153244e-9925-4460-92c2-7df5d9ca14e1

-- Sol generated from Algebra/BerggrenPriceInterlock/NNode.lean
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





/-! ### The Fermat pair of a factorisation -/


theorem fermatNode_eq {p q a b : ℤ} (hp : p = 2 * a + 1) (hq : q = 2 * b + 1) :
    fermatNode p q = (a + b + 1, b - a) := by
  have e1 : (p + q) / 2 = a + b + 1 := by omega
  have e2 : (q - p) / 2 = b - a := by omega
  simp only [fermatNode, e1, e2]

variable {p q : ℤ}








/-! ### The N-node lives in both trees -/





/-! ### Fermat's own scan -/




open BerggrenPrice in
theorem solution(hp : Odd p) (hq : Odd q) (h1 : 1 ≤ p) (hpq : p < q)
    (hco : IsCoprime p q) : IsNode (fermatNode p q) := by
  obtain ⟨a, ha⟩ := hp
  obtain ⟨b, hb⟩ := hq
  obtain ⟨x, y, hxy⟩ := hco
  rw [ha, hb] at hxy
  rw [fermatNode_eq ha hb]
  refine ⟨?_, ?_, ⟨x + y, y - x, ?_⟩, b, ?_⟩
  · show (1 : ℤ) ≤ b - a
    omega
  · show b - a < a + b + 1
    omega
  · show (x + y) * (a + b + 1) + (y - x) * (b - a) = 1
    linear_combination hxy
  · show a + b + 1 + (b - a) = 2 * b + 1
    omega
