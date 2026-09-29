-- Prove2me | Theorems.Thm_mme_exact_profile_boundary_end
-- name    : mme_exact_profile_boundary_end
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-22T18:38:33.327682+00:00
-- url     : https://prove2.me/theorems/2c6d3aa4-183c-4680-b806-283597581306
-- title:
--   Boundary end of exact profile data, with its dimension product
-- statement:
--   Exact boundary data yields a boundary end with an explicit dimension product.
--
--   The data is: a list of blocks, each assigned to a cell; for each cell, a grade triple summing to the block size, one of whose modes is zero; and, for each cell, a histogram of the words of the mode after the zero mode, with total the number of blocks in that cell and supported on words of the cell's grade in that mode.
--
--   Then there is a boundary end for the predicate saying that every block has its cell's grades and the exact all-mode histograms: the zero mode's word is constant, the next mode has the prescribed histogram and the last mode is its reflection. The product of the three matrix dimensions of the boundary end is the product, over cells, of the cell's multinomial coefficient times five to the number of ones in its words.
-- source:
--   Alman-Duan-Vassilevska Williams-Xu-Xu-Zhou, More Asymmetry Yields Faster Matrix Multiplication (https://arxiv.org/abs/2404.16349), section 6: the boundary cases of the recursive construction. General statement; no exponent claim.

import Mathlib
import Definitions.Def_mme_recursive_profiled_CW_data
open BigOperators MME MME.RecursiveYZ MME.RecursiveYZ.Boundary MME.CompleteSplit MME.ProfiledCW
open scoped Classical
set_option autoImplicit false

theorem mme_exact_profile_boundary_end {ell N L K : ℕ} (hL : L * 2 ^ (ell - 1) = N)
    (cell : Fin L → Fin K) (zero : Fin K → Fin 3) (grade : Fin K → Fin 3 → ℕ)
    (htotal : ∀ c, grade c 0 + grade c 1 + grade c 2 = 2 * 2 ^ (ell - 1))
    (hzero : ∀ c, grade c (zero c) = 0)
    (count : Fin K → CompleteWord ell → ℕ)
    (hcount : ∀ c, ∑ s, count c s = Fintype.card {p : Fin L // cell p = c})
    (hsupport : ∀ c s, count c s ≠ 0 → CWCells.grade s = grade c (zero c + 1)) :
    ∃ B : BoundaryEnd ell N (fun i x ↦
        (∀ p, CWCells.grade (split (Equiv.refl (Fin L)) hL x p) = grade (cell p) i) ∧
          Useful cell (fun c s ↦
            if i = zero c then (if s = (fun _ ↦ 0) then Fintype.card {p : Fin L // cell p = c} else 0)
            else if i = zero c + 1 then count c s else count c (flipLabel s))
            (split (Equiv.refl (Fin L)) hL x)),
      B.a * B.b * B.c = ∏ c : Fin K, ((Fintype.card {p : Fin L // cell p = c}).factorial /
        ∏ s, (count c s).factorial) * 5 ^ (∑ s, count c s * Boundary.ones s) := by sorry
