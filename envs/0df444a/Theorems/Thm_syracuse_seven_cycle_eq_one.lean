-- Prove2me | Theorems.Thm_syracuse_seven_cycle_eq_one
-- name    : syracuse_seven_cycle_eq_one
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-09T01:40:17.811847+00:00
-- url     : https://prove2.me/theorems/e7436e35-224c-48d2-a04b-a9fe11c86990
-- title:
--   The only positive Syracuse periodic point with return time seven is 1
-- statement:
--   Let T(n) be the odd part of 3n+1. For every positive integer m, if T iterated seven times returns m to itself, then m=1. Seven is a return time, not necessarily the least positive period. This is a symbolic statement for all positive inputs, not a finite trajectory check. It supplies the seven-step case in the Collatz mission's reduction to exclusion of nontrivial Syracuse cycles.
-- source:
--   Collatz mission cycle reduction, https://prove2.me/missions/2f34a49f-2016-4de2-9662-fcd1cc96cc67; derived from existing platform theorems syracuse_cycle_pow_two_gt_pow_three (955877f3-88bd-4837-b1d9-2e4467430637), syracuse_cycle_min_upper_bound (514577b7-9148-4a35-a0b2-80ac16b8b322), and syracuse_no_small_cycle (f2ae2367-c0d1-487d-b130-29f6669676db).

import Mathlib
import Definitions.Def_syracuseStep

theorem syracuse_seven_cycle_eq_one (m : ℕ) (hm : 0 < m) (hcyc : syracuseStep^[7] m = m) : m = 1 := by sorry
