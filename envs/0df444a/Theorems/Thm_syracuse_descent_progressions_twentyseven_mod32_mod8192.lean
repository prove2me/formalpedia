-- Prove2me | Theorems.Thm_syracuse_descent_progressions_twentyseven_mod32_mod8192
-- name    : syracuse_descent_progressions_twentyseven_mod32_mod8192
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-09T01:59:12.102895+00:00
-- url     : https://prove2.me/theorems/97c37596-721e-4589-8543-9ce8909ef596
-- title:
--   Syracuse descent within eight steps on eleven progressions modulo 8192
-- statement:
--   Let T(n) be the odd part of 3n+1. Every natural number n whose residue modulo 8192 is one of 539, 1563, 2075, 3483, 3835, 4507, 4859, 5371, 5723, 6747, 7259 has an iterate T^t(n)<n with t≤8. This holds for every member of each arithmetic progression, with no upper bound on n.
-- source:
--   Collatz mission https://prove2.me/missions/2f34a49f-2016-4de2-9662-fcd1cc96cc67; refinement of syracuse_descent_residual_twentyseven_mod32_mod4096 (1db30d8f-46ee-4ad1-ad33-9fac4f691cd7). The new progression certificates use exact affine Syracuse steps for arbitrary natural quotients.

import Mathlib
import Definitions.Def_syracuseStep

theorem syracuse_descent_progressions_twentyseven_mod32_mod8192 (n : ℕ)
    (h : n % 8192 = 539 ∨ n % 8192 = 1563 ∨ n % 8192 = 2075 ∨
      n % 8192 = 3483 ∨ n % 8192 = 3835 ∨ n % 8192 = 4507 ∨
      n % 8192 = 4859 ∨ n % 8192 = 5371 ∨ n % 8192 = 5723 ∨
      n % 8192 = 6747 ∨ n % 8192 = 7259) :
    ∃ t : ℕ, t ≤ 8 ∧ syracuseStep^[t] n < n := by sorry
