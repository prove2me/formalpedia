-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_potts_weighted_full_assignment_nonzero
-- name    : ZeroFreeRRG.Hardcore.potts_weighted_full_assignment_nonzero
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T08:49:02.642794+00:00
-- url     : https://prove2.me/theorems/41fb7fd1-6ae4-4495-bbcb-71f951ea70e2
-- title:
--   Fully fixed weighted Potts sums are nonzero
-- statement:
--   If every edge interaction is at distance less than one from $1$, the weighted Potts partition sum with all vertex colors fixed is nonzero.
-- source:
--   Auxiliary step for Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, Lemma 5.7.

import Mathlib
import Definitions.Def_ZeroFreeRRG_Hardcore_PottsWeighted
import Definitions.Def_ZeroFreeRRG_Hardcore_PottsPartial
set_option autoImplicit false
open ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem ZeroFreeRRG.Hardcore.potts_weighted_full_assignment_nonzero {V : Type} [Fintype V] (q : ℕ) (G : SimpleGraph V)
    (W : Sym2 V → Fin q → Fin q → ℂ) (hW : ∀ e i j, W e i j = W e j i)
    (τ : V → Fin q) (hbound : ∀ e ∈ G.edgeFinset, ∀ i j, ‖W e i j - 1‖ < 1) :
    pottsWeightedPartial q G W hW Finset.univ τ ≠ 0 := by sorry
