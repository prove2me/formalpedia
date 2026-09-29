-- Prove2me | Theorems.Thm_GeneratorTilt_sqrt_two_pos_p
-- name    : GeneratorTilt.sqrt_two_pos_p
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-18T00:44:11.633074+00:00
-- url     : https://prove2.me/theorems/d35f663d-d25e-4d34-ae28-cda8d1465d5b
-- title:
--   Sqrt two pos'
-- statement:
--   Formal statement of `GeneratorTilt.sqrt_two_pos'` from the Aether Catalog (Novelty). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem GeneratorTilt.sqrt_two_pos': (0:ℝ) < Real.sqrt 2 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/GeneratorTiltRatio.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/GeneratorTiltRatio.lean#L53

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




/-! ## Numeric facts about `√2` -/

theorem GeneratorTilt.sqrt_two_pos_p: (0:ℝ) < Real.sqrt 2 := by sorry
