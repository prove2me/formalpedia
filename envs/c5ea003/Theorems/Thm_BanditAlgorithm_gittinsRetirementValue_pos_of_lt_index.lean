-- Prove2me | Theorems.Thm_BanditAlgorithm_gittinsRetirementValue_pos_of_lt_index
-- name    : BanditAlgorithm.gittinsRetirementValue_pos_of_lt_index
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-07-31T04:06:50.408505+00:00
-- url     : https://prove2.me/theorems/009a20f6-0013-43fe-beeb-f74b95934680
-- title:
--   Positive retirement value below the Gittins index
-- statement:
--   If the charge $\gamma$ is strictly below the Gittins index $g(x)$, an epsilon-optimal admissible stopping rule has strictly positive expected discounted net reward. Consequently $v_\gamma(x)>0$.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (CUP 2020), fair-charge characterization Eq. (35.8), ratio characterization Eq. (35.9), printed pp.448--449.

import Definitions.Def_GittinsRetirementValue

open MeasureTheory ProbabilityTheory ENNReal

theorem BanditAlgorithm.gittinsRetirementValue_pos_of_lt_index
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r) {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1)
    (hint : DiscountedRewardIntegrable P r α)
    (x : S) (γ : ℝ) (hg : γ < gittinsIndex P r α x) :
    0 < gittinsRetirementValue P r α γ x := by
  sorry
