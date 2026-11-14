-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_potts_deterministic_zero_free
-- name    : ZeroFreeRRG.Hardcore.potts_deterministic_zero_free
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T08:37:17.586604+00:00
-- url     : https://prove2.me/theorems/4d45dc1c-94b0-44d0-8759-94e449f02a0f
-- title:
--   Potts zero-free disk near the independent-spin point
-- statement:
--   For $d\ge3$ and $q\ge2$, the Potts partition function of every finite simple graph of maximum degree at most $d$ is nonzero whenever $$|\beta-1|<0.35/d.$$ This is the Potts assertion of Lemma 5.7.
-- source:
--   Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, Lemma 5.7.

import Mathlib
import Definitions.Def_ZeroFreeRRG_Hardcore_Models
open scoped Classical

namespace ZeroFreeRRG.Hardcore
theorem potts_deterministic_zero_free (d : ℕ) (hd : 3 ≤ d) : ∀ q : ℕ, 2 ≤ q → ∀ (V : Type) [Fintype V] (G : SimpleGraph V), (∀ v, G.degree v ≤ d) → ∀ β : ℂ, ‖β - 1‖ < 0.35 / (d : ℝ) → pottsZ q G β ≠ 0 := by sorry
end ZeroFreeRRG.Hardcore
