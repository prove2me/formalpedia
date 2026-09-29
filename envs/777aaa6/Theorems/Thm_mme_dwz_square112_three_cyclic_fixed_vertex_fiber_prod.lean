-- Prove2me | Theorems.Thm_mme_dwz_square112_three_cyclic_fixed_vertex_fiber_prod
-- name    : mme_dwz_square112_three_cyclic_fixed_vertex_fiber_prod
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-08T08:17:21.747074+00:00
-- url     : https://prove2.me/theorems/b615f311-0b83-49bb-aaea-000e1d1bd27a
-- title:
--   Three-cyclic fixed-vertex fiber is a product of one-region fibers
-- statement:
--   Fix a length `N`, prescribed row multiplicities `c`, and a triple `v` of mode words whose grade multiplicities are the exact square112 marginals of `c`.
--
--   Consider triples of exact words indexed cyclically by the three tensor modes, subject to the condition that the `i`-th word induces the prescribed mode word `v i` in mode `i`. The number of such triples is exactly the product over the three modes of the corresponding one-region fibers:
--
--   $$ D = F_0 F_1 F_2, \qquad F_i = \prod_a \frac{(\text{marginal } c\, i\, a)!}{\prod_{r\,:\,\text{row } r\, i = a} (c_r)!}. $$
--
--   The constraint decouples across modes, so the fiber is a genuine product of the three single-mode fibers rather than merely being bounded by one. This supplies the degree count `D` used by the three-cyclic incidence certificate.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, FOCS 2023, arXiv:2210.10173v5, Section 7.2 (printed p. 66) and Equation (34) (p. 71), https://arxiv.org/abs/2210.10173v5

import Theorems.Thm_mme_dwz_square112_exact_profile_marginals_and_fibers

open MME.DWZSquare112
open scoped BigOperators

set_option autoImplicit false

theorem mme_dwz_square112_three_cyclic_fixed_vertex_fiber_prod
    (N : ℕ) (c : Fin 4 → ℕ) (v : Fin 3 → Fin N → Fin 3)
    (hv : ∀ i a : Fin 3, Fintype.card {j : Fin N // v i j = a} = marginal c i a) :
    Nat.card {t : Fin 3 → ExactWord N c // ∀ i, modeWord (t i) i = v i}
      = ∏ i : Fin 3, ∏ a : Fin 3,
          (marginal c i a).factorial /
            ∏ r : {r : Fin 4 // row r i = a}, (c r.1).factorial := by sorry
