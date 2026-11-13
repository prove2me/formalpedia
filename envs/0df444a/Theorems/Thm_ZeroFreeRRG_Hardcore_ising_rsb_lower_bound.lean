-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_ising_rsb_lower_bound
-- name    : ZeroFreeRRG.Hardcore.ising_rsb_lower_bound
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T05:13:24.005392+00:00
-- url     : https://prove2.me/theorems/15b08b1d-b1d7-4ec9-8368-8e74b4c09587
-- title:
--   Ising RSB threshold is at least the Kesten–Stigum value
-- statement:
--   For every integer $d\ge3$, the antiferromagnetic Ising replica-symmetry-breaking threshold satisfies
--
--   $$\beta_{\rm RSB}(d,2)\ge\frac{\sqrt{d-1}-1}{\sqrt{d-1}+1}.$$
--
--   This is the lower-bound direction of the Ising threshold identity (5), obtained from the weak Kesten–Stigum consequence of variational replica symmetry.
-- source:
--   Chen, Wang, and Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1461.pdf, equation (5), printed p. 6; derived using equation (26), printed p. 30.

import Definitions.Def_ZeroFreeRRG_Hardcore_PottsThresholds

namespace ZeroFreeRRG.Hardcore
/-- The Ising threshold is at least the Kesten–Stigum value. -/
theorem ising_rsb_lower_bound (d : ℕ) (hd : 3 ≤ d) :
    (Real.sqrt ((d : ℝ) - 1) - 1) / (Real.sqrt ((d : ℝ) - 1) + 1) ≤ betaRSB d 2 := by sorry
end ZeroFreeRRG.Hardcore
