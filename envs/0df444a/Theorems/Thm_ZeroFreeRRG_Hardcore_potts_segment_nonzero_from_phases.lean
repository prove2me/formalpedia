-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_potts_segment_nonzero_from_phases
-- name    : ZeroFreeRRG.Hardcore.potts_segment_nonzero_from_phases
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T09:04:17.651881+00:00
-- url     : https://prove2.me/theorems/f21db07b-8148-4217-bde8-f605e824991b
-- title:
--   Potts segment zero-freeness from phase coherence
-- statement:
--   Suppose that for every partial coloring and unassigned vertex, uniform nonvanishing of all one-vertex extensions over the allowed edge-weight segments implies that their phases at any given weights lie in a common unit chord ball of radius $1/2$. For $d\ge3$, $q\ge2$ and $|\beta-1|<0.35/d$, every restricted weighted Potts sum with interaction entries on the segment from $1$ to $\beta$ is nonzero. The phase-coherence implication is an explicit hypothesis.
-- source:
--   Auxiliary reduction for Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, Lemma 5.7.

import Mathlib
import Definitions.Def_ZeroFreeRRG_Hardcore_PottsSegment
set_option autoImplicit false
open MeasureTheory Set ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem ZeroFreeRRG.Hardcore.potts_segment_nonzero_from_phases (d q : ℕ) (hd : 3 ≤ d) (hq : 2 ≤ q)
    (V : Type) [Fintype V] (G : SimpleGraph V) (β : ℂ) (hβ : ‖β-1‖ < 0.35/(d:ℝ))
    (phase : ∀ (S : Finset V) (τ : V → Fin q) (v : V), v ∉ S →
      (∀ (W : Sym2 V → Fin q → Fin q → ℂ) (hW : ∀ e i j, W e i j = W e j i),
        pottsSegmentWeights q G β W → ∀ c : Fin q,
          pottsWeightedPartial q G W hW (insert v S) (Function.update τ v c) ≠ 0) →
      ∀ (W : Sym2 V → Fin q → Fin q → ℂ) (hW : ∀ e i j, W e i j = W e j i),
        pottsSegmentWeights q G β W → ∃ u : ℂ, ‖u‖ = 1 ∧ ∀ c : Fin q,
          ‖u - pottsWeightedPartial q G W hW (insert v S) (Function.update τ v c) /
            (‖pottsWeightedPartial q G W hW (insert v S) (Function.update τ v c)‖ : ℂ)‖ ≤ 1/2) :
    ∀ (W : Sym2 V → Fin q → Fin q → ℂ) (hW : ∀ e i j, W e i j = W e j i),
      pottsSegmentWeights q G β W → ∀ (S : Finset V) (τ : V → Fin q),
        pottsWeightedPartial q G W hW S τ ≠ 0 := by sorry
