-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_potts_partition_edge_phase
-- name    : ZeroFreeRRG.Hardcore.potts_partition_edge_phase
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T09:29:05.341811+00:00
-- url     : https://prove2.me/theorems/b1b7f908-39ea-4306-8377-51b444297780
-- title:
--   One-edge phase bound for the Potts partial partition function
-- statement:
--   For symmetric Potts edge weights lying on the segment from 1 to the complex activity, changing the weights on a single edge incident to a fixed vertex preserves nonvanishing and changes the normalized phase by at most the stated explicit bound, assuming nonvanishing and phase coherence for the relevant partial partition functions. This is an auxiliary step toward the Potts zero-free disk.
-- source:
--   Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, Lemma 5.7, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf

import Mathlib
import Definitions.Def_ZeroFreeRRG_Hardcore_PottsInduction
set_option autoImplicit false
open MeasureTheory Set ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem ZeroFreeRRG.Hardcore.potts_partition_edge_phase (d q : ℕ) (hd : 3 ≤ d) (hq : 2 ≤ q)
    (V : Type) [Fintype V] (G : SimpleGraph V) (β : ℂ) (hβ : ‖β-1‖ < 0.35/(d:ℝ))
    (S : Finset V) (τ : V → Fin q) (v u : V) (hv : v ∈ S) (he : s(v,u) ∈ G.edgeFinset)
    (hNZ : pottsNonzeroAt q G β S) (hC : pottsCoherentAt q G β S)
    (hNZplus : ∀ T : Finset V, S ⊂ T → pottsNonzeroAt q G β T)
    (W W' : Sym2 V → Fin q → Fin q → ℂ)
    (hW : ∀ e i j, W e i j = W e j i) (hW' : ∀ e i j, W' e i j = W' e j i)
    (hseg : pottsSegmentWeights q G β W) (hseg' : pottsSegmentWeights q G β W')
    (hother : ∀ e ≠ s(v,u), ∀ i j, W' e i j = W e i j) :
    let Z := pottsWeightedPartial q G W hW S τ
    let Z' := pottsWeightedPartial q G W' hW' S τ
    Z' ≠ 0 ∧ ‖Z/(‖Z‖:ℂ)-Z'/(‖Z'‖:ℂ)‖ ≤
      (25/23)*(‖β-1‖/((7/8:ℝ)*(1-‖β-1‖))) := by sorry
