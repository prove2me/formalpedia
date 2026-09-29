-- Prove2me | Theorems.Thm_mme_low_level_boundary_profile_oriented_dimensions
-- name    : mme_low_level_boundary_profile_oriented_dimensions
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T12:26:59.539396+00:00
-- url     : https://prove2.me/theorems/03804287-0b3f-4de3-bff9-fed6de9d99f5
-- title:
--   Reading elementary matrix dimensions from oriented cell grades
-- statement:
--   Let $B$ be an exact boundary profile on $L$ complete words at depth $\ell\le1$, and orient it with zero mode $z$. Write $(g_0,g_1,g_2)$ for its oriented grades. Its matrix dimensions are
--   \[
--   a=5^{L\mathbf1[g_1=0,\ g_0=1]},\qquad
--   b=5^{L\mathbf1[g_2=0,\ g_0=1]},\qquad
--   c=5^{L\mathbf1[g_0=0,\ g_1=1]}.
--   \]
--   Thus only the three orientations of the mixed grade pattern $(0,1,1)$ contribute nontrivial dimensions; all unmixed boundary cells contribute dimension one.
-- source:
--   Elementary exact boundary profiles and the regional parent-window matrix extraction.

import Definitions.Def_mme_recursive_yz_boundary_data

open BigOperators MME MME.CompleteSplit MME.RecursiveYZ
  MME.RecursiveYZ.CWCells MME.RecursiveYZ.Boundary
set_option autoImplicit false

theorem mme_low_level_boundary_profile_oriented_dimensions
    {ell L : ℕ} (B : Boundary.Profile ell L) (hlevel : ell ≤ 1) (z : Fin 3) :
    B.a z = 5 ^ (if B.shape z 1 = 0 ∧ B.shape z 0 = 1 then L else 0) ∧
    B.b z = 5 ^ (if B.shape z 2 = 0 ∧ B.shape z 0 = 1 then L else 0) ∧
    B.c z = 5 ^ (if B.shape z 0 = 0 ∧ B.shape z 1 = 1 then L else 0) := by sorry
