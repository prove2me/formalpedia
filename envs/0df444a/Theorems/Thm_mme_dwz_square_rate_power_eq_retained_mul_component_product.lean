-- Prove2me | Theorems.Thm_mme_dwz_square_rate_power_eq_retained_mul_component_product
-- name    : mme_dwz_square_rate_power_eq_retained_mul_component_product
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T13:33:25.366628+00:00
-- url     : https://prove2.me/theorems/ad9f6790-5302-49c3-ab4f-2a7a2066f2af
-- title:
--   Exact Equation-(25) rate factorization at every integral Table-2 scale
-- statement:
--   Let $M=10^{16}$ be the exact Table-2 scale, let $c_s=M\alpha_s$ be the integral component multiplicities, and let $B_s(\tau)$ be the fifteen positive component endpoints. For every real $\tau$ and natural $m$, the finite Equation-(25) endpoint factors exactly as $$\operatorname{squareRate}(\tau)^{Mm}=2^{MmR_{\mathrm{ret}}}\prod_{s=0}^{14}B_s(\tau)^{c_sm}.$$ Thus the retained-copy combinatorial factor and the literal product of component witnesses multiply to exactly the frozen square-rate endpoint, without an asymptotic or rounding gap.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Equation (25), Section 6.3 and Table 2; https://arxiv.org/abs/2210.10173

import Mathlib
import Definitions.Def_mme_dwz_square_data
import Definitions.Def_mme_dwz_table2_integer_counts
import Theorems.Thm_mme_dwz_table2_component_endpoint_product_eq_rate

open BigOperators Finset
open MME.DWZSquare

set_option autoImplicit false

theorem mme_dwz_square_rate_power_eq_retained_mul_component_product
    (tau : ℝ) (m : ℕ) :
    (squareRate tau) ^ (MME.DWZTable2Counts.scale * m) =
      Real.rpow 2
          (retainedLogRate *
            ((MME.DWZTable2Counts.scale * m : ℕ) : ℝ)) *
        (∏ s : Fin 15,
          (componentBase tau s) ^
            (MME.DWZTable2Counts.component s * m)) := by
  sorry
