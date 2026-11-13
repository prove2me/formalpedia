-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_ising_rsb_threshold
-- name    : ZeroFreeRRG.Hardcore.ising_rsb_threshold
-- status  : Open
-- author  : @wcysai
-- created : 2026-11-13T04:56:49.542261+00:00
-- url     : https://prove2.me/theorems/04e12238-6a12-4826-b961-6a734cd202fa
-- title:
--   Ising replica-symmetry-breaking threshold
-- statement:
--   For every integer $d\ge3$, the two-state antiferromagnetic Potts (Ising) replica-symmetry-breaking threshold equals
--
--   $$\beta_{\rm RSB}(d,2)=\frac{\sqrt{d-1}-1}{\sqrt{d-1}+1}.$$
--
--   The threshold is the Bethe positive-witness boundary of equation (32). This known identity is used in the paper to specialize its Potts results to Ising.
-- source:
--   Chen, Wang, and Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1461.pdf, equation (5), printed p. 6, citing [CLMS22].

import Definitions.Def_ZeroFreeRRG_Hardcore_PottsThresholds

namespace ZeroFreeRRG.Hardcore
/-- Equation (5): the two-state Potts threshold is the Kesten–Stigum threshold. -/
theorem ising_rsb_threshold (d : ℕ) (hd : 3 ≤ d) :
    betaRSB d 2 = (Real.sqrt ((d : ℝ) - 1) - 1) / (Real.sqrt ((d : ℝ) - 1) + 1) := by sorry
end ZeroFreeRRG.Hardcore
