-- Prove2me | Theorems.Thm_mme_CW_2376_exact_profile_induced_family
-- name    : mme_CW_2376_exact_profile_induced_family
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T17:09:39.220315+00:00
-- url     : https://prove2.me/theorems/263f7e20-abe0-4a7e-ab28-4d048061978c
-- title:
--   Induced Salem--Spencer family for the exact CW 2.376 profile
-- statement:
--   For every sufficiently large exact-profile scale $m$, there is a finite family $F_m$ of triples of five-grade words having precisely the fifteen joint multiplicities in equation (13). The family is mode-disjoint and induced in the coordinatewise support hypergraph: if a supported mixed address uses its three mode words from members $x,y,z$ of $F_m$, then $x=y=z$. Its cardinality satisfies
--
--   $$
--   \left(H\exp(-r_m)\right)^{3{,}000{,}000m}\le |F_m|,
--   $$
--
--   where $H$ is the reciprocal of the five marginal-frequency factors and $r_m=(m+1)^{-1/4}$.
--
--   This is the purely finite-combinatorial output of exact type selection, Salem--Spencer hashing, and collision deletion. The induced clause is essential: it rules out unintended supported tensor blocks assembled from three different retained addresses.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), multinomial counts (12)--(13), support equation I+J+K=4, and Salem--Spencer hashing/collision pruning on journal pp. 265 and 267--269; https://www.sciencedirect.com/science/article/pii/S0747717108800132

import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_mme_CW_2376_profile_induced_family
import Theorems.Thm_mme_behrend_explicit_threeAP_free
import Theorems.Thm_mme_3AP_free_no_collision
open MME Filter

theorem mme_CW_2376_exact_profile_induced_family :
    ∀ᶠ m : ℕ in atTop,
      ∃ F : Finset (CW2376ExactProfileAddress m),
        CW2376InducedModeDisjoint F ∧
        (cw2376ProfileCountBase *
            Real.exp (-(cw2376ProfileRate m))) ^
            (cw2376ProfileLength m) ≤ (F.card : ℝ) := by
  sorry
