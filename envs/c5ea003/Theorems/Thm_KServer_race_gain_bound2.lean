-- Prove2me | Theorems.Thm_KServer_race_gain_bound2
-- name    : KServer.race_gain_bound2
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-01T20:04:36.85113+00:00
-- url     : https://prove2.me/theorems/2820b3e0-f757-43d1-8dc9-e5a83950119f
-- title:
--   Anti-concentration gain of the coin race, padded form
-- statement:
--   The gain of the coin race, in the padded form usable after grid regridding. For the race of two side chunk systems with $\kappa$ clamped coins, clamp $\varepsilon > 0$ and sizes in $[0, c_B]$, let $N_b$ bound the expected number of coin steps at which either side's next chunk size falls below a floor $c_{Lo}' \in [\varepsilon, c_B + \varepsilon]$. Then the expected imbalance of the consumed side masses satisfies
--   $$\sqrt{\frac{(\kappa\, c_{Lo}'^2)^3}{8B^2 + 3\gamma^2 B}} - \kappa\varepsilon - (c_B + \varepsilon + c_{Lo}')\, N_b \;\le\; \mathbb{E}\,\lvert S_L - S_R\rvert,$$
--   where $B = \kappa\,(c_B+\varepsilon)^2$ and $\gamma = c_B+\varepsilon$. Unlike the pointwise-window form, no lower bound on the chunk sizes is assumed: the imbalance martingale is padded with synthetic $\pm c_{Lo}'$ fair coins on the out-of-window steps, restoring the pathwise variance window required by the anti-concentration inequality, and the discrepancy is charged to the expected bad-step count $N_b$, which the grid-regridded systems control via Chebyshev. This is the form of the gain used in the level recursion of the BCR lower bound.
-- source:
--   BCR randomized k-server lower bound, race construction

import Mathlib
import Definitions.Def_KServer_race_core
import Definitions.Def_KServer_race_gain
import Definitions.Def_KServer_race_pad

namespace KServer

open Race

theorem race_gain_bound2 {X : Type*} [MetricSpace X] {s t : X}
    {cB T pe : ℝ} {mL : ℕ}
    (A BL BR CC : ChunkSystemB X s t 0 cB T pe mL)
    (κ : ℕ) (ε : ℝ) (hε : 0 < ε) (hcB : 0 ≤ cB)
    {cLo' : ℝ} (hεLo : ε ≤ cLo') (hLocB : cLo' ≤ cB + ε)
    {Nb : ℝ} (hNb : ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
      * Nbad A BL BR CC κ cLo' ω ≤ Nb) :
    Real.sqrt (((κ : ℝ) * cLo' ^ 2) ^ 3
        / (8 * ((κ : ℝ) * (cB + ε) ^ 2) ^ 2
          + 3 * (cB + ε) ^ 2 * ((κ : ℝ) * (cB + ε) ^ 2)))
      - (κ : ℝ) * ε - (cB + ε + cLo') * Nb
      ≤ ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
          * |sumL A BL BR CC κ ω - sumR A BL BR CC κ ω| := by sorry

end KServer
