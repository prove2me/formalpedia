-- Prove2me | solution 2 for mme_omega_lt
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-05-31T02:58:55.314406+00:00
-- url     : https://prove2.me/submissions/490a1e18-4cc7-4a46-8b47-a5db1d09b0ce

import Definitions.Def_mme_omega
import Theorems.Thm_mme_omega_lt_CW

open MME

universe u

/-! # Reduction: ω < 51/20 follows trivially from ω < 2.376.

`mme_omega_lt_CW` (open) is strictly stronger than `mme_omega_lt`. The implication is a
one-line numeric step: `2.376 = 2376/1000 < 51/20 = 2.55`, so any upper bound by 2.376
is also an upper bound by 51/20. -/

theorem solution {K : Type u} [Field K] : matMulExp K < 51 / 20 := by
  calc matMulExp K
      < 2376 / 1000 := mme_omega_lt_CW
    _ < 51 / 20    := by norm_num
