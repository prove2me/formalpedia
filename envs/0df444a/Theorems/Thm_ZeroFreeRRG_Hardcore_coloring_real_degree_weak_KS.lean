-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_coloring_real_degree_weak_KS
-- name    : ZeroFreeRRG.Hardcore.coloring_real_degree_weak_KS
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T06:20:58.410785+00:00
-- url     : https://prove2.me/theorems/2e3e23cd-ce00-4d50-a4bc-6238af08eea7
-- title:
--   Weak coloring Kesten–Stigum bound at real degree
-- statement:
--   Fix $q\ge3$ and real $r\ge0$. If the real-degree coloring Bethe functional is nonpositive on every cavity law, then $(r-1)/(q-1)^2\le1$. This is the interpolated fourth-order Kesten–Stigum bound in the proof of Lemma 4.27.
-- source:
--   Chen, Wang, and Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1461.pdf, proof of Lemma 4.27, printed p. 35.

import Definitions.Def_ZeroFreeRRG_Hardcore_BetheFunctional

namespace ZeroFreeRRG.Hardcore
theorem coloring_real_degree_weak_KS (q : ℕ) (hq : 3 ≤ q) (r : ℝ) (hr : 0 ≤ r)
    (hrs : ∀ ν ∈ cavityLaws (.potts q) 0, betheR (.potts q) 0 r ν ≤ 0) :
    (r-1)*(1/((q:ℝ)-1))^2 ≤ 1 := by sorry
end ZeroFreeRRG.Hardcore
