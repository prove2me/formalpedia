-- Prove2me | Definitions.Def_Shared_RainbowAPPairThreshold
-- name    : Shared_RainbowAPPairThreshold
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T15:13:20.516243+00:00
-- url     : https://prove2.me/theorems/b17a2104-978d-4a70-abda-81c81e7dbde0
-- title:
--   Aether Catalog definitions — Shared_RainbowAPPairThreshold
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.RainbowAPPairThreshold`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/RainbowAPPairThreshold.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Shared_RainbowAPSpectrumThreshold

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

namespace RainbowAP

/-- The rainbow pair-spectrum threshold with `k` colours. -/
noncomputable def T (k : ℕ) : ℕ := spectrumThreshold (Fin k × Fin k)









end RainbowAP


