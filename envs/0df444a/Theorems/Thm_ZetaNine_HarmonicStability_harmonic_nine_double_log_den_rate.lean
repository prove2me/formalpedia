-- Prove2me | Theorems.Thm_ZetaNine_HarmonicStability_harmonic_nine_double_log_den_rate
-- name    : ZetaNine.HarmonicStability.harmonic_nine_double_log_den_rate
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-03T14:05:47.148988+00:00
-- url     : https://prove2.me/theorems/6c9f6988-64e9-43e9-9ee6-6ecc0e61d8ac
-- title:
--   The reduced ninth harmonic denominator has rate eighteen at double endpoints
-- statement:
--   For the actual rational ninth-order harmonic sum at the double endpoint, $\log\operatorname{den}(H_{2M}^{(9)})/M\to18$ as $M\to\infty$ through natural numbers. There are no hypotheses; the factor eighteen is nine times the exact endpoint scaling factor two. This supplies the harmonic denominator baseline in the right-shifted Mellin construction.
-- source:
--   https://github.com/Anchen0823/zeta9-research-notes/releases/tag/research-2026-10-02; research/harmonic-denominator-stability-2026-10-01.md, sections 2 and 3; research/mellin-shift-arithmetic-2026-10-01.md. Original verified Lean source: missions/zeta9/formalization/PNTTransfer.lean, lines 143–147, SHA256 6c56d052ae48b44e76d40e7a08fcfd6ca8d232b5bc7882430bfbf48b85bb2c8b.

import Definitions.Def_ZetaNine_HarmonicStability
import Definitions.Def_ZetaNine_HarmonicPrimeValuation
import Mathlib.NumberTheory.Chebyshev

set_option autoImplicit false
open Filter
open ZetaNine.HarmonicStability

theorem ZetaNine.HarmonicStability.harmonic_nine_double_log_den_rate :
    Tendsto (fun M : ℕ => logDen (harmonicPower 9 (2 * M)) / (M : ℝ))
      atTop (nhds 18):= by sorry
