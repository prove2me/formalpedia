-- Prove2me | Theorems.Thm_ZetaNine_HarmonicStability_harmonic_log_den_rate
-- name    : ZetaNine.HarmonicStability.harmonic_log_den_rate
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-03T14:05:41.933221+00:00
-- url     : https://prove2.me/theorems/a4d7220e-a967-499d-a96b-5d020a46e1d3
-- title:
--   The reduced generalized harmonic denominator has rate equal to its positive order
-- statement:
--   For every fixed positive natural number $s$, write $H_N^{(s)}=\sum_{j=1}^N j^{-s}$ in lowest terms. Then $\log\operatorname{den}(H_N^{(s)})/N\to s$ along all natural $N\to\infty$. The only hypothesis is $s>0$. The prime-number-theorem inputs and the harmonic baseline are proved in the complete solution rather than assumed.
-- source:
--   https://github.com/Anchen0823/zeta9-research-notes/releases/tag/research-2026-10-02; research/harmonic-denominator-stability-2026-10-01.md, sections 2 and 3; research/mellin-shift-arithmetic-2026-10-01.md. Original verified Lean source: missions/zeta9/formalization/PNTTransfer.lean, lines 128–133, SHA256 6c56d052ae48b44e76d40e7a08fcfd6ca8d232b5bc7882430bfbf48b85bb2c8b.

import Definitions.Def_ZetaNine_HarmonicStability
import Definitions.Def_ZetaNine_HarmonicPrimeValuation
import Mathlib.NumberTheory.Chebyshev

set_option autoImplicit false
open Filter
open ZetaNine.HarmonicStability

theorem ZetaNine.HarmonicStability.harmonic_log_den_rate (s : ℕ) (hs : 0 < s) :
    Tendsto (fun N : ℕ => logDen (harmonicPower s N) / (N : ℝ))
      atTop (nhds (s : ℝ)):= by sorry
