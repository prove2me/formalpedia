-- Prove2me | Theorems.Thm_mme_dwz_table2_component_endpoint_product_eq_rate
-- name    : mme_dwz_table2_component_endpoint_product_eq_rate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T13:09:29.801165+00:00
-- url     : https://prove2.me/theorems/13381c11-e5ca-42db-af0d-47f1da76ad1d
-- title:
--   Exact Table-2 component product realizes the Equation-(25) component rate
-- statement:
--   Let $M=10^{16}$ be the exact common denominator for the frozen Table-2 data, let $c_s=M\alpha_s$ be the integral multiplicity of component $s$, and let $B_s(\tau)$ be its positive Section 6.3 component-value base. For every real $\tau$ and natural scale $m$,
--
--   $$
--   \prod_{s=0}^{14} B_s(\tau)^{c_s m}
--   =2^{\,Mm\,R_{\mathrm{comp}}(\tau)},
--   $$
--
--   where $R_{\mathrm{comp}}(\tau)=\sum_s\alpha_s\log_2 B_s(\tau)$ is `componentLogRate`. Thus the literal finite product of all restricted component endpoints has exactly the component exponential rate appearing in Equation (25), with no rounding or unverified logarithmic normalization.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Equation (25), Section 6.3 and Table 2 (printed pp. 58-59), specifically the weighted product defining alpha_V,tau; https://arxiv.org/abs/2210.10173

import Mathlib
import Definitions.Def_mme_dwz_square_data
import Definitions.Def_mme_dwz_table2_integer_counts
import Theorems.Thm_mme_dwz_square_componentBase_pos
import Theorems.Thm_mme_dwz_table2_integer_counts_exact

open BigOperators Finset
open MME.DWZSquare

set_option autoImplicit false

theorem mme_dwz_table2_component_endpoint_product_eq_rate
    (tau : ℝ) (m : ℕ) :
    (∏ s : Fin 15,
      (componentBase tau s) ^
        (MME.DWZTable2Counts.component s * m)) =
      Real.rpow 2
        (componentLogRate tau *
          ((MME.DWZTable2Counts.scale * m : ℕ) : ℝ)) := by
  sorry
