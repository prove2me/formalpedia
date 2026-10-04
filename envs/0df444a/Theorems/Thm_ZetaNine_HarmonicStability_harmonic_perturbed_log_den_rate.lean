-- Prove2me | Theorems.Thm_ZetaNine_HarmonicStability_harmonic_perturbed_log_den_rate
-- name    : ZetaNine.HarmonicStability.harmonic_perturbed_log_den_rate
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-03T14:06:01.062961+00:00
-- url     : https://prove2.me/theorems/490b871a-06b7-49c4-9053-05de764299d5
-- title:
--   Small-denominator perturbations preserve the unconditional harmonic denominator rate
-- statement:
--   For every fixed positive natural order $s$ and every rational sequence $r_N$ such that $\log\operatorname{den}(r_N)/N\to0$, one has $\log\operatorname{den}(H_N^{(s)}+r_N)/N\to s$. The perturbation is arbitrary subject to its stated sublinear logarithmic denominator condition. The harmonic baseline and prime-number-theorem inputs are proved; they are not extra hypotheses.
-- source:
--   https://github.com/Anchen0823/zeta9-research-notes/releases/tag/research-2026-10-02; research/harmonic-denominator-stability-2026-10-01.md, sections 2 and 3; research/mellin-shift-arithmetic-2026-10-01.md. Original verified Lean source: missions/zeta9/formalization/PNTTransfer.lean, lines 135–141, SHA256 6c56d052ae48b44e76d40e7a08fcfd6ca8d232b5bc7882430bfbf48b85bb2c8b.

import Definitions.Def_ZetaNine_HarmonicStability
import Definitions.Def_ZetaNine_HarmonicPrimeValuation
import Mathlib.NumberTheory.Chebyshev

set_option autoImplicit false
open Filter
open ZetaNine.HarmonicStability

theorem ZetaNine.HarmonicStability.harmonic_perturbed_log_den_rate (s : ℕ) (hs : 0 < s) (r : ℕ → ℚ)
    (hr : Tendsto (fun N => logDen (r N) / (N : ℝ)) atTop (nhds 0)) :
    Tendsto (fun N : ℕ => logDen (harmonicPower s N + r N) / (N : ℝ))
      atTop (nhds (s : ℝ)):= by sorry
