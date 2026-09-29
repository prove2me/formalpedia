-- Prove2me | Theorems.Thm_mme_fintype_constrained_prescribed_fiber_function_nonempty
-- name    : mme_fintype_constrained_prescribed_fiber_function_nonempty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T11:18:55.302063+00:00
-- url     : https://prove2.me/theorems/7a696ece-ba34-4ffe-8ef6-e5738d746a79
-- title:
--   Existence of finite constrained prescribed-fiber labelings
-- statement:
--   Let finite sets $A,B,I$ carry maps $h:A\to I$ and $q:B\to I$, and prescribe a nonnegative multiplicity $k_b$ for every $b\in B$. Suppose that within each coarse class $i\in I$, the prescribed multiplicities sum to the number of source elements in that class:
--
--   $$\sum_{b:q(b)=i} k_b = |\{a:h(a)=i\}|. $$
--
--   Then there exists a labeling $g:A\to B$ satisfying $q(g(a))=h(a)$ for every $a$, with exactly $k_b$ elements labeled by each $b$. This is the existence counterpart of the constrained multinomial counting formula.
-- source:
--   Standard finite multinomial combinatorics; applied to the fiberwise split-label construction in Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5.

import Theorems.Thm_mme_fintype_constrained_prescribed_fiber_function_card
import Mathlib.Data.Nat.Choose.Multinomial

open BigOperators

set_option autoImplicit false

theorem mme_fintype_constrained_prescribed_fiber_function_nonempty
    {alpha beta iota : Type*}
    [Fintype alpha] [DecidableEq alpha]
    [Fintype beta] [DecidableEq beta]
    [Fintype iota] [DecidableEq iota]
    (h : alpha → iota) (q : beta → iota) (k : beta → ℕ)
    (hsum : ∀ i,
      (∑ b : {b : beta // q b = i}, k b.1) =
        Fintype.card {a : alpha // h a = i}) :
    Nonempty
      {g : alpha → beta //
        (∀ a, q (g a) = h a) ∧
        ∀ b, Fintype.card {a // g a = b} = k b} := by
  sorry
