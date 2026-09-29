-- Prove2me | Theorems.Thm_mme_recursive_yz_boundary_actual_matrix_extraction
-- name    : mme_recursive_yz_boundary_actual_matrix_extraction
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-13T12:55:20.049349+00:00
-- url     : https://prove2.me/theorems/b426ad57-c86c-4a68-9ff2-d8055c1f7ead
-- title:
--   Exact-profile boundary cells yield their full matrix tensor
-- statement:
--   Every exact-profile boundary CW5 cell restricts to a matrix-multiplication tensor with the full factorial/power-of-five dimension. For zero mode X, Y or Z the dimensions are respectively (1,1,M), (M,1,1) or (1,M,1). The source is the actual CW5 power projected in all three canonical word bases by its grades and complementary complete profiles. The proof constructs the mode maps; no source factorization or extraction is assumed.
-- source:
--   Alman et al., More Asymmetry Yields Faster Matrix Multiplication, https://arxiv.org/html/2404.16349v2#S6, Remark 6.1 and Theorem 6.2; exact finite-profile form used in the recursive constituent stage.

import Definitions.Def_mme_recursive_yz_boundary_data
open MME MME.TensorObj
set_option autoImplicit false
universe u

theorem mme_recursive_yz_boundary_actual_matrix_extraction {K : Type u} [Field K] {ell L : ℕ}
    (B : MME.RecursiveYZ.Boundary.Profile ell L) (z : Fin 3) :
    Restrict (MMObj K (B.a z) (B.b z) (B.c z)) (B.tensor K z) := by sorry
