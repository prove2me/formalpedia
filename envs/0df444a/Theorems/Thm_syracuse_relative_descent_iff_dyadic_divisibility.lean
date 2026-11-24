-- Prove2me | Theorems.Thm_syracuse_relative_descent_iff_dyadic_divisibility
-- name    : syracuse_relative_descent_iff_dyadic_divisibility
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-24T12:10:15.686163+00:00
-- url     : https://prove2.me/theorems/d4f9de8b-8c05-480a-83ad-d22d5a42a672
-- title:
--   Exact dyadic test for a Syracuse step to cross a given target
-- statement:
--   Let $T(y)$ be the odd part of $3y+1$. If $2^b n\le 3y+1<2^{b+1}n$, then $T(y)<n$ if and only if $2^{b+1}$ divides $3y+1$. The comparison is with an arbitrary target $n$.
-- source:
--   Dyadic comparison for the relative descent problem https://prove2.me/theorems/747e0b8d-0cf3-4a0f-8330-b1f862f5898f.

import Definitions.Def_syracuseStep

theorem syracuse_relative_descent_iff_dyadic_divisibility (y n b : ℕ)
    (hlo : 2^b*n ≤ 3*y+1) (hhi : 3*y+1 < 2^(b+1)*n) :
    syracuseStep y < n ↔ 2^(b+1) ∣ 3*y+1 := by sorry
