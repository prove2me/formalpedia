-- Prove2me | Theorems.Thm_collatz_root_assumptions_no_uniform_meeting_bound
-- name    : collatz_root_assumptions_no_uniform_meeting_bound
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T11:14:52.976797+00:00
-- url     : https://prove2.me/theorems/da1b841f-250c-5fc0-8cb9-740011289643
-- title:
--   Arbitrarily late smaller-orbit meetings under the exact Collatz frontier hypotheses
-- statement:
--   For each pair of ordinary step limits and each size cutoff, there is a larger n satisfying every hypothesis of the original residual fifteen-modulo-sixteen milestone for which no smaller integer meets its orbit within the pair of limits.
-- source:
--   A standalone lemma for https://prove2.me/theorems/be9c3278-d7aa-42c6-a8d9-c9b925b1847b.

import Definitions.Def_collatzStepMap
import Definitions.Def_collatzMinPreimage
import Mathlib.Logic.Function.Iterate

theorem collatz_root_assumptions_no_uniform_meeting_bound (I T N : ℕ) :
    ∃ n : ℕ, N≤n ∧ 2310000≤n ∧ n%16=15 ∧
      (n%9=0 ∨ n%9=1 ∨ n%9=3 ∨ n%9=6 ∨ n%9=7) ∧
      (∀ t : ℕ, t≤128 → n≤collatzMinPreimage 16 (collatzStep^[t] n)) ∧
      n%81≠10 ∧ (n%2304≠1743 ∧ n%2304≠1599) ∧
      (n%4608≠2847 ∧ n%4608≠735 ∧ n%4608≠991 ∧
        n%4608≠2527 ∧ n%4608≠3039 ∧ n%4608≠4575) ∧
      n%2187 ∉ ([205,325,919,991,1000,1090,1171,2170] : List ℕ) ∧
      ∀ k a b : ℕ, k<n → a≤I → b≤T → collatzStep^[a] n≠collatzStep^[b] k := by sorry
