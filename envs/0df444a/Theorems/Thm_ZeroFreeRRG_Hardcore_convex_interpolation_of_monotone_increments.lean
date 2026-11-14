-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_convex_interpolation_of_monotone_increments
-- name    : ZeroFreeRRG.Hardcore.convex_interpolation_of_monotone_increments
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T06:29:56.245822+00:00
-- url     : https://prove2.me/theorems/f7d330a4-b51e-4f46-b31f-05ae9a7ad00f
-- title:
--   Convexity of a piecewise-linear extension
-- statement:
--   Let $(v_n)_{n\ge0}$ be a real sequence with nondecreasing successive differences. Its piecewise-linear extension, which equals $(1-t+n)v_n+(t-n)v_{n+1}$ for $n=\lfloor t\rfloor$, is convex on $[0,\infty)$. This isolates the interpolation step used in the proof of Lemma 4.27.
-- source:
--   Chen, Wang, and Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1461.pdf, proof of Lemma 4.27, printed p. 34.

import Mathlib
open Set

namespace ZeroFreeRRG.Hardcore
theorem convex_interpolation_of_monotone_increments (v : ℕ → ℝ)
    (hv : ∀ n, v (n+1)-v n ≤ v (n+2)-v (n+1)) :
    ConvexOn ℝ (Ici 0) (fun x =>
      (1-x+(⌊x⌋₊:ℝ))*v ⌊x⌋₊ + (x-(⌊x⌋₊:ℝ))*v (⌊x⌋₊+1)) := by sorry
end ZeroFreeRRG.Hardcore
