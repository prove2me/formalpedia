-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_potts_weighted_segment_nonzero
-- name    : ZeroFreeRRG.Hardcore.potts_weighted_segment_nonzero
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T08:49:48.988354+00:00
-- url     : https://prove2.me/theorems/fe1c49b3-0496-4fd1-91e7-842b4aab038c
-- title:
--   Zero-freeness for restricted Potts sums with segment-valued edge weights
-- statement:
--   Let $d\ge3$, $q\ge2$, and let a finite graph have maximum degree at most $d$. Fix any subset of vertices and prescribe their colors. Suppose all symmetric edge interaction entries lie on the complex segment joining $1$ to $\beta$, where $|\beta-1|<0.35/d$. The restricted weighted Potts partition sum is nonzero. This stronger induction target implies the Potts assertion of Lemma 5.7.
-- source:
--   Auxiliary induction target for Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, Lemma 5.7.

import Mathlib
import Definitions.Def_ZeroFreeRRG_Hardcore_PottsWeighted
open MeasureTheory Set ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem ZeroFreeRRG.Hardcore.potts_weighted_segment_nonzero (d q : ℕ) (hd : 3 ≤ d) (hq : 2 ≤ q)
    (V : Type) [Fintype V] (G : SimpleGraph V) (hG : ∀ v, G.degree v ≤ d)
    (β : ℂ) (hβ : ‖β-1‖ < 0.35/(d:ℝ))
    (W : Sym2 V → Fin q → Fin q → ℂ) (hW : ∀ e i j, W e i j = W e j i)
    (hseg : ∀ e ∈ G.edgeFinset, ∀ i j, ∃ t : ℝ, t ∈ Icc 0 1 ∧ W e i j = 1+(t:ℂ)*(β-1))
    (S : Finset V) (τ : V → Fin q) : pottsWeightedPartial q G W hW S τ ≠ 0 := by sorry
