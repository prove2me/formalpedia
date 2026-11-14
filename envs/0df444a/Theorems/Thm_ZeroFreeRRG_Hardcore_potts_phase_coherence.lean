-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_potts_phase_coherence
-- name    : ZeroFreeRRG.Hardcore.potts_phase_coherence
-- status  : Open
-- author  : @wcysai
-- created : 2026-11-13T09:06:48.120961+00:00
-- url     : https://prove2.me/theorems/e74ea45e-4a21-4d26-8f6f-c1b5dcbabc35
-- title:
--   Phase coherence for restricted Potts sums
-- statement:
--   For $d\ge3$, $q\ge2$, and $|\beta-1|<0.35/d$, suppose a graph has maximum degree at most $d$ and every one-vertex extension of a partial coloring has nonzero weighted Potts sum uniformly over interactions on the segment from $1$ to $\beta$. Then, at any such interaction matrix, the normalized phases of these extension sums all lie within distance $1/2$ of a common unit complex number. This is the remaining phase-coherence step for the Potts zero-free disk.
-- source:
--   Auxiliary induction target for Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, Lemma 5.7.

import Mathlib
import Definitions.Def_ZeroFreeRRG_Hardcore_PottsSegment
open MeasureTheory Set ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem ZeroFreeRRG.Hardcore.potts_phase_coherence (d q : ℕ) (hd : 3 ≤ d) (hq : 2 ≤ q)
    (V : Type) [Fintype V] (G : SimpleGraph V) (hG : ∀ v, G.degree v ≤ d)
    (β : ℂ) (hβ : ‖β-1‖ < 0.35/(d:ℝ))
    (S : Finset V) (τ : V → Fin q) (v : V) (hv : v ∉ S)
    (hchild : ∀ (W : Sym2 V → Fin q → Fin q → ℂ) (hW : ∀ e i j, W e i j = W e j i),
      pottsSegmentWeights q G β W → ∀ c : Fin q,
        pottsWeightedPartial q G W hW (insert v S) (Function.update τ v c) ≠ 0)
    (W : Sym2 V → Fin q → Fin q → ℂ) (hW : ∀ e i j, W e i j = W e j i)
    (hseg : pottsSegmentWeights q G β W) :
    ∃ u : ℂ, ‖u‖ = 1 ∧ ∀ c : Fin q,
      ‖u - pottsWeightedPartial q G W hW (insert v S) (Function.update τ v c) /
        (‖pottsWeightedPartial q G W hW (insert v S) (Function.update τ v c)‖ : ℂ)‖ ≤ 1/2 := by sorry
