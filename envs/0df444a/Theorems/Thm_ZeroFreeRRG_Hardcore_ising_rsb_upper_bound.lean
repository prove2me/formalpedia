-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_ising_rsb_upper_bound
-- name    : ZeroFreeRRG.Hardcore.ising_rsb_upper_bound
-- status  : Open
-- author  : @wcysai
-- created : 2026-11-13T05:13:26.046894+00:00
-- url     : https://prove2.me/theorems/d0d04a75-3fd5-4a77-84a9-8daf24c927cf
-- title:
--   Ising RSB threshold is at most the Kesten–Stigum value
-- statement:
--   For every integer $d\ge3$, the antiferromagnetic Ising replica-symmetry-breaking threshold satisfies
--
--   $$\beta_{\rm RSB}(d,2)\le\frac{\sqrt{d-1}-1}{\sqrt{d-1}+1}.$$
--
--   This is the upper-bound direction of the threshold identity (5).
-- source:
--   Chen, Wang, and Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1461.pdf, equation (5), printed p. 6, citing [CLMS22].

import Definitions.Def_ZeroFreeRRG_Hardcore_PottsThresholds

namespace ZeroFreeRRG.Hardcore
/-- The Ising threshold is at most the Kesten–Stigum value. -/
theorem ising_rsb_upper_bound (d : ℕ) (hd : 3 ≤ d) :
    betaRSB d 2 ≤ (Real.sqrt ((d : ℝ) - 1) - 1) / (Real.sqrt ((d : ℝ) - 1) + 1) := by sorry
end ZeroFreeRRG.Hardcore
