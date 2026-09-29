-- Prove2me | solution 1 for BerggrenPrice.primitive_triple
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T11:50:48.621984+00:00
-- url     : https://prove2.me/submissions/c18f8b78-ec31-4531-b9b0-516e9cf44809

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



/-- The odd leg of a node is genuinely odd. -/
theorem oddLeg_odd {v : Node} (h : IsNode v) : Odd (oddLeg v) := by
  obtain ⟨-, -, -, s, hs⟩ := h
  have hm : v.1 = 2 * s + 1 - v.2 := by omega
  refine ⟨2 * s * (s - v.2) + s + (s - v.2), ?_⟩
  simp only [oddLeg, hm]; ring


/-! ### The Fermat pair of a factorisation -/



variable {p q : ℤ}








/-! ### The N-node lives in both trees -/





/-! ### Fermat's own scan -/




open BerggrenPrice in
theorem solution{v : Node} (h : IsNode v) : IsCoprime (oddLeg v) (evenLeg v) := by
  obtain ⟨t, ht⟩ := oddLeg_odd h
  obtain ⟨-, -, ⟨x, y, hxy⟩, -⟩ := h
  have c2 : IsCoprime (oddLeg v) (2 : ℤ) := ⟨1, -t, by rw [ht]; ring⟩
  have cm : IsCoprime (oddLeg v) v.1 :=
    ⟨-y ^ 2, x * (1 + y * v.2) + y ^ 2 * v.1, by
      simp only [oddLeg]; linear_combination (y * v.2 + 1) * hxy⟩
  have cn : IsCoprime (oddLeg v) v.2 :=
    ⟨x ^ 2, 2 * y - y ^ 2 * v.2 + x ^ 2 * v.2, by
      simp only [oddLeg]; linear_combination (x * v.1 - y * v.2 + 1) * hxy⟩
  have := (c2.mul_right cm).mul_right cn
  simpa [evenLeg] using this
