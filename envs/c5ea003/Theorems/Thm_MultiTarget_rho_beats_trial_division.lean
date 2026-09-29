-- Prove2me | Theorems.Thm_MultiTarget_rho_beats_trial_division
-- name    : MultiTarget.rho_beats_trial_division
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:57:12.208194+00:00
-- url     : https://prove2.me/theorems/3f72d06f-1264-4f30-8851-bae6903905a6
-- title:
--   Exponent dominance.
-- statement:
--   **Exponent dominance.**  For every constant `C > 0`, the `N^{1/4}` cost of
--   Pollard-ρ beats the `C`-free trial-division cost `N^{1/2}` for all `N > C⁴`.
--   Hence the relaxed multi-target search (exponent `1/2`) is asymptotically
--   dominated no matter how good its constants are.
--
--   ```lean
--   theorem MultiTarget.rho_beats_trial_division{C N : ℝ} (hC : 0 < C) (hN : C ^ 4 < N) :
--       C * N ^ ((1:ℝ)/4) < N ^ ((1:ℝ)/2) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/MultiTargetTrialDivision.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/MultiTargetTrialDivision.lean#L133

-- Thm stub generated from Bridges/MultiTargetTrialDivision.lean
import Mathlib
import Definitions.Def_Bridges_MultiTargetTrialDivision
import Definitions.Def_Bridges_TreeSieveLottery

/-!
# The multi-target relaxation is exactly trial division

This file formalises the analysis of the "MULTI-TARGET" relaxation
(round-72 experiment `exp558`).  A tree search whose goal is the *exact* target
`a = N` is relaxed to the much weaker goal `gcd (a, N) > 1`.  Empirically the
relaxation is a `~10^12` speedup over blind FIFO search, but `100 %` of first
hits land at `a = min (p, q)`, with fitted exponent `α = 1.087`, `r² = 1.0`:
dead centre of the trial-division band.  The theorems below explain *why* this
is forced, not accidental.

Main results.

* `firstHit_eq_min` / `isLeast_hit_min` — the least `a ≥ 2` with `gcd (a, N) > 1`
  is **exactly** `min p q` for a semiprime `N = p * q`.  Any search that sweeps
  values in ascending order therefore always first hits at `min p q`; the
  observed histogram is a theorem, not a statistic.
* `min_sq_le` / `ascending_sweep_is_trial_division` — the cost of the ascending
  sweep is `min p q ≤ √N`: exactly the trial-division exponent `1/2`.
* `relaxation_speedup_exact` — relative to the exact target `a = N`, the
  relaxation saves precisely a factor `max p q`, which is between `√N` and
  `N / 2`: a huge but strictly bounded win.
* `rho_beats_trial_division` — the `N^{1/4}` cost of Pollard-ρ beats
  `C · N^{1/2}`-class trial division for every constant `C` once `N > C⁴`;
  so the relaxed search remains dominated.
* `tree_integer_face_trichotomy` — the capstone: any splitter reading a value
  off the integer face of the Berggren tree is in one of three regimes —
  integer square identity (returns `N`, no split), a genuine mod-`N` congruence
  of squares (Dixon/QS class), or an ascending value sweep (trial division,
  cost `min p q`).  Every route ends in a known method.
-/

open MultiTarget

open TreeSieve

/-! ## The ascending sweep first-hit theorem -/







/-! ## The cost of the sweep is the trial-division exponent -/






/-! ## Pollard-ρ still dominates -/

theorem MultiTarget.rho_beats_trial_division{C N : ℝ} (hC : 0 < C) (hN : C ^ 4 < N) :
    C * N ^ ((1:ℝ)/4) < N ^ ((1:ℝ)/2) := by sorry
