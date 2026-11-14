-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_potts_edge_row_replacement
-- name    : ZeroFreeRRG.Hardcore.potts_edge_row_replacement
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T09:15:24.594868+00:00
-- url     : https://prove2.me/theorems/cf37bc31-4886-4897-bb75-4d311499eac9
-- title:
--   Symmetric row replacement preserving the Potts segment
-- statement:
--   Given symmetric edge interactions taking values on a common segment, an edge and two colors a,b, there is a new symmetric interaction system that preserves every other edge and the common segment and whose row a on the chosen edge equals its old row b.
-- source:
--   Supporting step for Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, Lemma 5.7.

import Mathlib
import Definitions.Def_ZeroFreeRRG_Hardcore_PottsSegment
set_option autoImplicit false
open MeasureTheory Set ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem ZeroFreeRRG.Hardcore.potts_edge_row_replacement {V : Type} [Fintype V] (q : ℕ) (G : SimpleGraph V) (β : ℂ)
    (W : Sym2 V → Fin q → Fin q → ℂ) (hW : ∀ e i j, W e i j = W e j i)
    (hseg : pottsSegmentWeights q G β W) (e₀ : Sym2 V) (a b : Fin q) :
    ∃ W' : Sym2 V → Fin q → Fin q → ℂ,
      (∀ e i j, W' e i j = W' e j i) ∧ pottsSegmentWeights q G β W' ∧
      (∀ e ≠ e₀, ∀ i j, W' e i j = W e i j) ∧
      (∀ j, W' e₀ a j = W e₀ b j) := by sorry
