-- Prove2me | solution 1 for mme_dwz_square_rate_power_eq_retained_mul_component_product
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T13:37:34.55584+00:00
-- url     : https://prove2.me/submissions/e7bb69d8-2a03-4e3e-b452-b5e29189d0b5

import Mathlib
import Definitions.Def_mme_dwz_square_data
import Definitions.Def_mme_dwz_table2_integer_counts
import Theorems.Thm_mme_dwz_table2_component_endpoint_product_eq_rate

open BigOperators Finset
open MME.DWZSquare

set_option autoImplicit false
set_option warningAsError true

theorem solution
    (tau : ℝ) (m : ℕ) :
    (squareRate tau) ^ (MME.DWZTable2Counts.scale * m) =
      Real.rpow 2
          (retainedLogRate *
            ((MME.DWZTable2Counts.scale * m : ℕ) : ℝ)) *
        (∏ s : Fin 15,
          (componentBase tau s) ^
            (MME.DWZTable2Counts.component s * m)) := by
  rw [squareRate]
  rw [← Real.rpow_natCast]
  change ((2 : ℝ) ^ (retainedLogRate + componentLogRate tau)) ^
      ((MME.DWZTable2Counts.scale * m : ℕ) : ℝ) = _
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  rw [show
    (retainedLogRate + componentLogRate tau) *
        ((MME.DWZTable2Counts.scale * m : ℕ) : ℝ) =
      retainedLogRate *
          ((MME.DWZTable2Counts.scale * m : ℕ) : ℝ) +
        componentLogRate tau *
          ((MME.DWZTable2Counts.scale * m : ℕ) : ℝ) by
    ring]
  rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  change
    ((2 : ℝ) ^
        (retainedLogRate *
          ((MME.DWZTable2Counts.scale * m : ℕ) : ℝ))) *
      ((2 : ℝ) ^
        (componentLogRate tau *
          ((MME.DWZTable2Counts.scale * m : ℕ) : ℝ))) =
    ((2 : ℝ) ^
        (retainedLogRate *
          ((MME.DWZTable2Counts.scale * m : ℕ) : ℝ))) *
      (∏ s : Fin 15,
        (componentBase tau s) ^
          (MME.DWZTable2Counts.component s * m))
  congr 1
  exact (mme_dwz_table2_component_endpoint_product_eq_rate tau m).symm
