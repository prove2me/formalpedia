-- Prove2me | Theorems.Thm_GeneratorTilt_criticalRatio_mem_balance_band
-- name    : GeneratorTilt.criticalRatio_mem_balance_band
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:58:06.418462+00:00
-- url     : https://prove2.me/theorems/74ed08e5-66f1-42e5-89e2-c689d46dd77a
-- title:
--   The critical ratio lies strictly inside the balance band.
-- statement:
--   **The critical ratio lies strictly inside the balance band.**  Enforcing `q < 2p` (the
--   band `r ∈ [1,2]`) does *not* determine the winner: the sign of the scan-order effect flips
--   at `r★ ≈ 1.3726`, strictly between `1` and `2`.
--
--   ```lean
--   theorem GeneratorTilt.criticalRatio_mem_balance_band: 1 < criticalRatio ∧ criticalRatio < 2 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/GeneratorTiltRatio.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/GeneratorTiltRatio.lean#L145

-- Thm stub generated from Novelty/GeneratorTiltRatio.lean
import Mathlib
import Definitions.Def_Novelty_GeneratorTiltRatio
/-
# The prime-ratio law of generator tilt (continuous layer)

Companion to `Novelty.GeneratorTiltWindow`.  There the winner of the scan-order contest was
reduced to a single scalar, the mean tilt `z̄` of a pool of semiprimes inside the canonical
window `(√(N/2), √N]`.  Here we compute that scalar *from the generator*: for a semiprime
`N = p q` with ratio `r = q/p`, the tilt of the small factor is

`zOfRatio r = (r^{-1/2} - 2^{-1/2}) / (1 - 2^{-1/2})`,

a strictly decreasing map with `zOfRatio 1 = 1` and `zOfRatio 2 = 0`
(`tilt_eq_zOfRatio`, `zOfRatio_strictAntiOn`, `zOfRatio_one`, `zOfRatio_two`).

Consequences proved here:

* `zOfRatio_criticalRatio` / `half_lt_zOfRatio_iff` — the **critical ratio** at which the two
  scan orders tie is exactly `r★ = 24 - 16√2 ≈ 1.3726`, and a pool is top-heavy (so
  sqrt-descending wins, by `GeneratorTilt.descending_wins_iff_top_heavy`) iff its ratio is
  *below* `r★`.  Since `1 < r★ < 2` (`criticalRatio_mem_balance_band`), the sign of the
  effect flips strictly *inside* the balance band: enforcing `q < 2p` is not enough.
* `integral_zOfRatio` — the hard-balance control value: a ratio-uniform pool on `[1,2]` has
  mean tilt exactly `√2 - 1 = 0.41421…`, matching the analytic control `0.414` and the
  measured `0.4114 [0.3887, 0.4341]`; its tilt-only speedup is exactly `√2`
  (`predictor_at_uniform_balance`), against a measured `1.5896 ± 0.0538`.
* `zOfRatio_five_quarters_bracket` — a deployed-style pool with effective ratio `5/4` has
  tilt in `(0.63, 0.64)`, i.e. top-heavy, reproducing the measured `0.6356
  [0.6150, 0.6562]`; window-ascending then *loses*.

So the Λ-channel (window-ascending) advantage is confined to generator classes whose ratio
mass sits above `r★`, and it is *not* implied by balance.
-/

open GeneratorTilt

open Real



/-! ## Numeric facts about `√2` -/







/-! ## Values and monotonicity -/




/-! ## The bridge: geometric tilt equals the ratio law -/


/-! ## The critical ratio -/

theorem GeneratorTilt.criticalRatio_mem_balance_band: 1 < criticalRatio ∧ criticalRatio < 2 := by sorry
