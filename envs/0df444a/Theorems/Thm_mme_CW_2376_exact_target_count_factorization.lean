-- Prove2me | Theorems.Thm_mme_CW_2376_exact_target_count_factorization
-- name    : mme_CW_2376_exact_target_count_factorization
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T23:35:34.129903+00:00
-- url     : https://prove2.me/theorems/85e5e8fa-a725-44d2-803c-baa38745c5b3
-- title:
--   The exact CW target count factors into mode words and target completions
-- statement:
--   Let $N$ be the CW profile length, let $V=N!/(∏_r A_r!)$ be the number of possible words with the prescribed five-grade marginal, and let $D_*=(∏_r A_r!)/(∏_σ β_σ!)$ be the optimized completion degree over one fixed mode word. Then the complete exact-target family satisfies
--
--   $$
--   |T|=V D_*,
--   $$
--
--   and $D_*≥1$. The proof verifies the two factorial divisibility chains before passing from natural-number multinomial quotients to real division.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), multinomial target and completion counts on journal pp. 267--269; https://doi.org/10.1016/S0747-7171(08)80013-2

import Definitions.Def_mme_CW_2376_marginal_joint_tables
import Theorems.Thm_mme_CW_2376_exact_profile_address_nat_card
import Theorems.Thm_mme_CW_2376_all_exact_target_edges_card
import Theorems.Thm_mme_CW_2376_target_joint_table_marginal

open MME BigOperators

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

theorem mme_CW_2376_exact_target_count_factorization (m : ℕ) :
    let N := cw2376ProfileLength m
    let V : ℝ :=
      (N.factorial : ℝ) /
        (∏ r : Fin 5, ((cw2376MarginalMultiplicity m r).factorial : ℝ))
    ((cw2376AllExactTargetEdges m).card : ℝ) =
        V * (cw2376TargetStarDegree m : ℝ) ∧
      1 ≤ cw2376TargetStarDegree m := by
  sorry
