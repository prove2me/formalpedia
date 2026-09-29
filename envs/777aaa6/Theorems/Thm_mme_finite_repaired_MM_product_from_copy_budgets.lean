-- Prove2me | Theorems.Thm_mme_finite_repaired_MM_product_from_copy_budgets
-- name    : mme_finite_repaired_MM_product_from_copy_budgets
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-13T12:07:12.700972+00:00
-- url     : https://prove2.me/theorems/0eb821a0-6ecd-4503-ad5d-063dd4093d78
-- title:
--   Exact repaired matrix-tensor assembly from finite copy budgets
-- statement:
--   For each factor j, let c_j be the available count and r_j its positive repair group size, with c_j at least r_j. Suppose the global repair divisor R is at least the product of 2r_j. The tensor product of floor(c_j/r_j) copies of local matrix tensors then restricts to floor(product(c_j)/R) independent matrix tensors with the products of the three local dimensions. This is a finite integer statement, including a zero-factor product, and uses no assumed tensor assembly map.
-- source:
--   Finite tensor-algebra and integer-rounding step for Alman et al., More Asymmetry Yields Faster Matrix Multiplication, https://arxiv.org/html/2404.16349v2#S6.SS5, Sections 6.5–6.6, combining repaired independent copies. The explicit factor 2 per product factor accounts for floors.

import Definitions.Def_mme_rank_bridge
import Definitions.Def_mme_CW_2376_address_block
open BigOperators MME MME.TensorObj
set_option autoImplicit false
universe u

theorem mme_finite_repaired_MM_product_from_copy_budgets {K : Type u} [Field K] {k R : ℕ}
    (a b c counts repair : Fin k → ℕ)
    (hpos : ∀ j, 0 < repair j)
    (henough : ∀ j, repair j ≤ counts j)
    (hR : (∏ j, 2 * repair j) ≤ R) :
    Restrict
      (bigAdd (fun _ : Fin ((∏ j, counts j) / R) ↦
        MMObj K (∏ j, a j) (∏ j, b j) (∏ j, c j)))
      (kronFin k (fun j ↦ bigAdd (fun _ : Fin (counts j / repair j) ↦
        MMObj K (a j) (b j) (c j))))  := by sorry
