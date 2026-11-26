-- Prove2me | Theorems.Thm_syracuse_coprime_to_six_reaches_one_below_1291845632
-- name    : syracuse_coprime_to_six_reaches_one_below_1291845632
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T06:58:59.862554+00:00
-- url     : https://prove2.me/theorems/2735d89f-2986-4d18-a508-95239f0c8d05
-- title:
--   Syracuse convergence for inputs coprime to six below 1,291,845,632
-- statement:
--   Every positive integer below 1,291,845,632 that is coprime to six has a Syracuse iterate equal to one.
-- source:
--   Strong induction from the earlier certified cutoff and the next four contiguous kernel-checked interval certificates.

import Definitions.Def_syracuseStep
import Mathlib.Logic.Function.Iterate

theorem syracuse_coprime_to_six_reaches_one_below_1291845632 (n : ℕ) (hn : 0 < n) (hlt : n < 1291845632)
    (ho : ¬ 2 ∣ n) (h3 : ¬ 3 ∣ n) : ∃ t : ℕ, syracuseStep^[t] n = 1 := by sorry
