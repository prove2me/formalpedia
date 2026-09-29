-- Prove2me | Theorems.Thm_mme_low_level_boundary_profile_dimension
-- name    : mme_low_level_boundary_profile_dimension
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T12:27:26.959621+00:00
-- url     : https://prove2.me/theorems/d210d623-684d-4521-b138-466575bc5406
-- title:
--   Elementary boundary-profile dimensions
-- statement:
--   Let $B$ be an exact boundary profile on $L$ complete words at depth $\ell\le1$, with free grade $i$. Its exact matrix dimension is
--   \[
--   \dim B=\begin{cases}5^L,&i=1,\\1,&i\ne1.\end{cases}
--   \]
--   This includes $L=0$. At elementary depth the grade determines the whole word, so there is no multinomial contribution to the dimension.
-- source:
--   Elementary exact boundary profiles and the regional parent-window matrix extraction.

import Definitions.Def_mme_recursive_yz_boundary_data

open BigOperators MME MME.CompleteSplit MME.RecursiveYZ
  MME.RecursiveYZ.CWCells MME.RecursiveYZ.Boundary
set_option autoImplicit false

theorem mme_low_level_boundary_profile_dimension
    {ell L : ℕ} (B : Boundary.Profile ell L) (hlevel : ell ≤ 1) :
    B.dim = if B.index = 1 then 5 ^ L else 1 := by sorry
