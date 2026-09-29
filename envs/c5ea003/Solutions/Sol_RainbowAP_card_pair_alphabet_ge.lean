-- Prove2me | solution 1 for RainbowAP.card_pair_alphabet_ge
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T01:19:09.080248+00:00
-- url     : https://prove2.me/submissions/ff2cdcc3-26c7-468e-8bd9-697291469761

-- Sol generated from Shared/RainbowAPPairThreshold.lean
import Mathlib
import Definitions.Def_Shared_RainbowAPPairThreshold
import Theorems.Thm_RainbowAP_card_pair_alphabet

/-!
# The rainbow pair-spectrum threshold `T_k` and its exact `Θ(k² log k)` growth

Fix a palette of `k` colours.  A colouring of a block-decomposed interval realises the
*full pair spectrum* if every one of the `k²` ordered colour pairs `(i, j)` occurs on some
2-term arithmetic progression of the decomposition.  `T k` is the least number of blocks at
which a strict majority of colourings has full pair spectrum; formally it is the full-spectrum
threshold of the alphabet `Fin k × Fin k`.

Main results.

* `RainbowAP.T_lower_bound` : `2 k² log k - 2 log k ≤ T k`.
* `RainbowAP.T_upper_bound` : `T k ≤ 2 k² log k + k² log 2 + 1`.
* `RainbowAP.T_theta`       : explicit constants `c₁ = 1`, `c₂ = 4` with
  `0.1 ≤ c₁ ≤ c₂ ≤ 10` sandwiching `T k` between `c₁ k² log k` and `c₂ k² log k` for `k ≥ 2`.
* `RainbowAP.T_tendsto_two` : `T k / (k² log k) → 2`, so the optimal constants coincide,
  `c₁ = c₂ = 2`.
* `RainbowAP.T_liminf`, `RainbowAP.T_limsup` : the `lim inf` and the `lim sup` both equal `2`.
-/

open Finset Real Filter Topology

open RainbowAP











open RainbowAP in
lemma solution(k : ℕ) (hk : 2 ≤ k) : 2 ≤ Fintype.card (Fin k × Fin k) := by
  rw [card_pair_alphabet]
  nlinarith
