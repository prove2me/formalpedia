-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_relative_entropy_pointwise_nonnegative
-- name    : ZeroFreeRRG.Hardcore.relative_entropy_pointwise_nonnegative
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T06:36:32.97144+00:00
-- url     : https://prove2.me/theorems/4eace94e-4cb7-4fd3-90d3-bdf4adb8412d
-- title:
--   Pointwise relative-entropy gap is nonnegative
-- statement:
--   For real numbers $p\ge0$ and $q>0$, the relative-entropy gap $p\log p-p\log q-p+q$ is nonnegative, with $0\log0=0$. This pointwise inequality underlies the nonnegativity of relative entropy used in Lemma 4.27.
-- source:
--   Chen, Wang, and Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1461.pdf, proof of Lemma 4.27, printed p. 34.

import Mathlib

namespace ZeroFreeRRG.Hardcore
theorem relative_entropy_pointwise_nonnegative (p q : ℝ) (hp : 0 ≤ p) (hq : 0 < q) :
    0 ≤ p * Real.log p - p * Real.log q - p + q := by sorry
end ZeroFreeRRG.Hardcore
