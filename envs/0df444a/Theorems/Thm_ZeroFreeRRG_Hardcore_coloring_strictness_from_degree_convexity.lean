-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_coloring_strictness_from_degree_convexity
-- name    : ZeroFreeRRG.Hardcore.coloring_strictness_from_degree_convexity
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T06:13:07.851978+00:00
-- url     : https://prove2.me/theorems/56e8013a-7229-4caa-a0ac-eef93bded275
-- title:
--   Coloring Bethe uniqueness from degree convexity and slack
-- statement:
--   Fix integers $d\ge3$ and $q\ge2$, and a real degree $r>d$. Suppose the coloring Bethe functional is convex in its nonnegative degree for each nontrivial cavity law, and is nonpositive at degree $r$ for all cavity laws. Then the Bethe functional at degree $d$ is strictly negative for every nontrivial cavity law (Condition 1). This establishes the convexity interpolation step in Lemma 4.27, with convexity retained as an explicit hypothesis.
-- source:
--   Chen, Wang, and Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1461.pdf, proof of Lemma 4.27, printed pp. 34–35.

import Definitions.Def_ZeroFreeRRG_Hardcore_BetheFunctional
open scoped Classical
open Set

namespace ZeroFreeRRG.Hardcore
theorem coloring_strictness_from_degree_convexity (d q : ℕ) (hd : 3 ≤ d) (hq : 2 ≤ q) (r : ℝ) (hr : (d:ℝ) < r)
    (hconv : ∀ ν ∈ cavityLaws (.potts q) 0, ν ≠ diracPi (.potts q) 0 →
      ConvexOn ℝ (Ici 0) (fun s => betheR (.potts q) 0 s ν))
    (hrs : ∀ ν ∈ cavityLaws (.potts q) 0, betheR (.potts q) 0 r ν ≤ 0) :
    Condition1 (.potts q) d 0 := by sorry
end ZeroFreeRRG.Hardcore
