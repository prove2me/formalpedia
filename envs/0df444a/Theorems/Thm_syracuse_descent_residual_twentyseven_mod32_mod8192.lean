-- Prove2me | Theorems.Thm_syracuse_descent_residual_twentyseven_mod32_mod8192
-- name    : syracuse_descent_residual_twentyseven_mod32_mod8192
-- status  : Open
-- author  : @mysticflounder
-- created : 2026-09-09T01:59:11.932721+00:00
-- url     : https://prove2.me/theorems/49dbc3ef-38df-4573-ac0c-ef1b9c35f45a
-- title:
--   Remaining Syracuse descent classes congruent to 27 modulo 32, refined modulo 8192
-- statement:
--   Let T(n) be the odd part of 3n+1. Suppose n is congruent to 27 modulo 32 and avoids the following classes: 59 modulo 128; 123 and 219 modulo 256; 347, 507, and 923 modulo 1024; 1019, 1435, 1787, 2203, 2587, 2907, and 3675 modulo 4096; and 539, 1563, 2075, 3483, 3835, 4507, 4859, 5371, 5723, 6747, 7259 modulo 8192. Prove that some iterate of T is strictly smaller than n. This is the open remainder after the known descent progressions are removed; no uniform bound on the number of steps is asserted.
-- source:
--   Collatz mission https://prove2.me/missions/2f34a49f-2016-4de2-9662-fcd1cc96cc67; refinement of syracuse_descent_residual_twentyseven_mod32_mod4096 (1db30d8f-46ee-4ad1-ad33-9fac4f691cd7). The new progression certificates use exact affine Syracuse steps for arbitrary natural quotients.

import Mathlib
import Definitions.Def_syracuseStep

theorem syracuse_descent_residual_twentyseven_mod32_mod8192 (n : ℕ)
    (h : n % 32 = 27)
    (h128 : n % 128 ≠ 59)
    (h256 : n % 256 ≠ 123 ∧ n % 256 ≠ 219)
    (h1024 : n % 1024 ≠ 347 ∧ n % 1024 ≠ 507 ∧ n % 1024 ≠ 923)
    (h4096 : n % 4096 ≠ 1019 ∧ n % 4096 ≠ 1435 ∧ n % 4096 ≠ 1787 ∧
      n % 4096 ≠ 2203 ∧ n % 4096 ≠ 2587 ∧ n % 4096 ≠ 2907 ∧
      n % 4096 ≠ 3675)
    (h8192 : n % 8192 ≠ 539 ∧ n % 8192 ≠ 1563 ∧ n % 8192 ≠ 2075 ∧
      n % 8192 ≠ 3483 ∧ n % 8192 ≠ 3835 ∧ n % 8192 ≠ 4507 ∧
      n % 8192 ≠ 4859 ∧ n % 8192 ≠ 5371 ∧ n % 8192 ≠ 5723 ∧
      n % 8192 ≠ 6747 ∧ n % 8192 ≠ 7259) :
    ∃ t : ℕ, syracuseStep^[t] n < n := by sorry
