-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_size_bias_strict_product_event
-- name    : ZeroFreeRRG.Hardcore.size_bias_strict_product_event
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T07:27:39.787318+00:00
-- url     : https://prove2.me/theorems/144edfa4-987c-4817-bd75-08bb94182bc1
-- title:
--   Positive-probability strict event for independent couplings
-- statement:
--   Let $d\ge2$ and let $\pi$ be a probability law on pairs such that $X<Y$ and $X>0$ each have positive probability. For $d$ independent pairs from $\pi$, the event that the first two pairs satisfy $X<Y$ and every other pair has $X>0$ has positive probability. This is the strict event used in the hardcore monotonicity proof.
-- source:
--   Chen, Wang, and Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1461.pdf, proof of Lemma 4.17, printed p. 30.

import Mathlib
open scoped BigOperators
open MeasureTheory Set

namespace ZeroFreeRRG.Hardcore
theorem size_bias_strict_product_event (d : ℕ) (hd : 2 ≤ d) (π : Measure (ℝ × ℝ)) [IsProbabilityMeasure π]
    (hs : 0 < π {p | p.1 < p.2}) (hp : 0 < π {p | 0 < p.1}) :
    0 < (Measure.pi fun _ : Fin d => π)
      {xs | (xs ⟨0,by omega⟩).1 < (xs ⟨0,by omega⟩).2 ∧
        (xs ⟨1,by omega⟩).1 < (xs ⟨1,by omega⟩).2 ∧
        ∀ a, a ≠ ⟨0,by omega⟩ → a ≠ ⟨1,by omega⟩ → 0 < (xs a).1} := by sorry
end ZeroFreeRRG.Hardcore
