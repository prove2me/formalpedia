-- Prove2me | Theorems.Thm_mme_stothers_fixed_outer_hash_budget
-- name    : mme_stothers_fixed_outer_hash_budget
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T20:02:52.17301+00:00
-- url     : https://prove2.me/theorems/7b268aac-a715-442d-a9dc-df162f637a03
-- title:
--   Affine-hash target surplus for the fixed Stothers profile
-- statement:
--   Let $N_m$ be the length of the exact fixed Stothers profile and let $V_m=N_m!/(A_0!⋯ A_8!)$ be the number of words with its prescribed one-coordinate marginal. For every sufficiently large scale $m$, there is a vertex-closed retained family $E_m$ in the marginally regular outer-address hypergraph for which
--
--   $$C(E_m)+V_m e^{-10^6 √(N_m+1)} ≤ T(E_m).$$
--
--   Here $T(E_m)$ counts retained exact-joint-profile target edges and $C(E_m)$ counts directed target-to-ambient coordinate collisions. Consequently deterministic pruning retains an induced family of size at least the displayed surplus. The numerical constant is deliberately loose and only records a subexponential loss.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, Lemma 3.3 and Equations (3.3)--(3.4), specialized to the exact stationary profile in Section 5. The proof uses the standard Salem--Spencer affine-hash extraction and collision deletion.

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Nat.Factorial.NatCast
import Definitions.Def_mme_stothers_fixed_outer_profile

open BigOperators Filter

set_option autoImplicit false

theorem mme_stothers_fixed_outer_hash_budget :
    ∀ᶠ m : ℕ in Filter.atTop,
      let N := MME.StothersFourth.fixedOuterLength m
      let V : ℝ :=
        (N.factorial : ℝ) /
          ∏ j : Fin 9,
            ((MME.StothersFourth.fixedMarginalCount m j).factorial : ℝ)
      ∃ E : Finset (MME.StothersFourth.FixedMarginalSupportedAddress m),
        MME.StothersFourth.FixedMarginalVertexClosed E ∧
        ((MME.StothersFourth.fixedTargetAmbientCollisions E).card : ℝ) +
            V * Real.exp
              (-1000000 * Real.sqrt (((N + 1 : ℕ) : ℝ))) ≤
          ((MME.StothersFourth.fixedExactTargetEdges E).card : ℝ) := by
  sorry
