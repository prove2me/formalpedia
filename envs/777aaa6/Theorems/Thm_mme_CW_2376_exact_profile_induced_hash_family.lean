-- Prove2me | Theorems.Thm_mme_CW_2376_exact_profile_induced_hash_family
-- name    : mme_CW_2376_exact_profile_induced_hash_family
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T17:25:32.256907+00:00
-- url     : https://prove2.me/theorems/6fe15884-2850-4ea3-98e7-2c550a6e4ea9
-- title:
--   Finite induced Salem--Spencer pruning for the exact CW 2.376 profile
-- statement:
--   Let N=3,000,000m and impose exactly the fifteen joint multiplicities from equation (13). For all sufficiently large m, the Salem--Spencer hash and collision-deletion construction produces a family F of exact-profile addresses that is both mode-disjoint and fully induced in the coordinatewise support hypergraph. If V=N!/(A_0!A_1!A_2!A_3!A_4!) is the exact number of words in one mode, where the five marginals are (384072,1308290,1231903,75036,699)m, then |F| is at least V exp(-100000 sqrt(N+1)). The large numerical constant is a conservative explicit envelope for the Behrend density and polynomial collision-pruning factors. The induced clause is essential: every supported mixed triple among retained mode words must come from one and the same retained address.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), equations (12)--(13), hashing and collision pruning on journal pp. 267--269; https://www.sciencedirect.com/science/article/pii/S0747717108800132

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Nat.Factorial.NatCast
import Definitions.Def_mme_CW_2376_profile_induced_family
import Theorems.Thm_mme_behrend_explicit_threeAP_free
import Theorems.Thm_mme_3AP_free_no_collision
open MME Filter

theorem mme_CW_2376_exact_profile_induced_hash_family :
    ∀ᶠ m : ℕ in atTop,
      let N := cw2376ProfileLength m
      let V : ℝ :=
        (N.factorial : ℝ) /
          (((384072 * m).factorial : ℝ) *
            ((1308290 * m).factorial : ℝ) *
            ((1231903 * m).factorial : ℝ) *
            ((75036 * m).factorial : ℝ) *
            ((699 * m).factorial : ℝ))
      ∃ F : Finset (CW2376ExactProfileAddress m),
        CW2376InducedModeDisjoint F ∧
        V * Real.exp
          (-100000 * Real.sqrt (((N + 1 : ℕ) : ℝ))) ≤
            (F.card : ℝ) := by
  sorry
