-- Prove2me | Theorems.Thm_MultiTarget_min_le_of_hit
-- name    : MultiTarget.min_le_of_hit
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:56:55.550882+00:00
-- url     : https://prove2.me/theorems/69466feb-bab6-4078-9a2c-898da95965d8
-- title:
--   Any hit is at least the smaller prime factor of a semiprime.
-- statement:
--   Any hit is at least the smaller prime factor of a semiprime.
--
--   ```lean
--   theorem MultiTarget.min_le_of_hit{p q : ℕ} (hp : p.Prime) (hq : q.Prime) {a : ℕ}
--       (h : Hit (p * q) a) : min p q ≤ a := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/MultiTargetTrialDivision.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/MultiTargetTrialDivision.lean#L47

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

theorem MultiTarget.min_le_of_hit{p q : ℕ} (hp : p.Prime) (hq : q.Prime) {a : ℕ}
    (h : Hit (p * q) a) : min p q ≤ a := by sorry
