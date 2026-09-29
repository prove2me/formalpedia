-- Prove2me | Theorems.Thm_mme_CW_2376_full_marginal_hash_target_collision_budget
-- name    : mme_CW_2376_full_marginal_hash_target_collision_budget
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T20:21:17.688918+00:00
-- url     : https://prove2.me/theorems/868b7147-1239-44a9-aec8-6226bab4298e
-- title:
--   Full-marginal Salem--Spencer target collision budget
-- statement:
--   Let $N=3{,}000{,}000m$ and let $V$ be the exact number of mode words with the five optimized marginals. For all sufficiently large $m$, the affine Coppersmith--Winograd hash into a Salem--Spencer set produces a retained full marginal-supported hypergraph $E$ that is vertex-closed. If $T(E)$ is its dominant equation-(13) target part and $C(T,E)$ is the set of directed collisions from a target edge to any ambient edge, then
--
--   $$
--   |C(T,E)|+V exp(-100000 sqrt(N+1)) ≤ |T(E)|.
--   $$
--
--   This is the sole remaining randomized/counting leaf in the outer 2.376 extraction. It must hash the full marginal-supported hypergraph, not only target-profile edges. Its counting uses the exact target completion degree
--
--   $$
--   D_* = (∏_{g=0}^4 A_g!) / ((699m)!^3(37518m)!^6(307638m)!^3(616627m)!^3),
--   $$
--
--   the full compatible degree $D_{all}$ from equation (12), the product-form dominance bound $D_{all} ≤ (N+1)^{15}D_*$, a modulus comparable to $D_{all}$, and the Behrend density. Directed target--ambient collision counting is what preserves full inducedness without paying for collisions between two non-target edges.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), equations (12)--(13), Salem--Spencer hashing and usual pruning on journal pp. 267--269; https://doi.org/10.1016/S0747-7171(08)80013-2

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Nat.Factorial.NatCast
import Definitions.Def_mme_CW_2376_marginal_hash_state
import Theorems.Thm_mme_behrend_explicit_threeAP_free
import Theorems.Thm_mme_3AP_free_no_collision

open MME Filter

theorem mme_CW_2376_full_marginal_hash_target_collision_budget :
    ∀ᶠ m : ℕ in atTop,
      let N := cw2376ProfileLength m
      let V : ℝ :=
        (N.factorial : ℝ) /
          (((384072 * m).factorial : ℝ) *
            ((1308290 * m).factorial : ℝ) *
            ((1231903 * m).factorial : ℝ) *
            ((75036 * m).factorial : ℝ) *
            ((699 * m).factorial : ℝ))
      ∃ E : Finset (CW2376MarginalSupportedAddress m),
        CW2376MarginalVertexClosed E ∧
        ((cw2376TargetAmbientCollisions E).card : ℝ) +
            V * Real.exp
              (-100000 * Real.sqrt (((N + 1 : ℕ) : ℝ))) ≤
          ((cw2376ExactTargetEdges E).card : ℝ) := by
  sorry
