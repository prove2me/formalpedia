-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_potts_row_set_properties
-- name    : ZeroFreeRRG.Hardcore.potts_row_set_properties
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T09:22:31.953113+00:00
-- url     : https://prove2.me/theorems/1fe7e66a-8f3d-487f-9b22-5ed268c894f1
-- title:
--   Properties of simultaneous symmetric row replacements
-- statement:
--   For symmetric Potts interactions whose edge coefficients lie on a common segment, replacing row a by row b on any finite edge set, together with its matching column, preserves symmetry and the common segment, leaves all other edges unchanged, and makes row a equal to the former row b on each selected edge.
-- source:
--   Auxiliary step for Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, Lemma 5.7.

import Mathlib
import Definitions.Def_ZeroFreeRRG_Hardcore_PottsRowChain
set_option autoImplicit false
open MeasureTheory Set ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem ZeroFreeRRG.Hardcore.potts_row_set_properties {V : Type} [Fintype V] (q : ℕ) (G : SimpleGraph V) (β : ℂ)
    (W : Sym2 V → Fin q → Fin q → ℂ) (hW : ∀ e i j, W e i j = W e j i)
    (hseg : pottsSegmentWeights q G β W) (F : Finset (Sym2 V)) (a b : Fin q) :
    let W' := pottsReplaceRows W F a b
    (∀ e i j, W' e i j = W' e j i) ∧ pottsSegmentWeights q G β W' ∧
      (∀ e ∉ F, ∀ i j, W' e i j = W e i j) ∧
      (∀ e ∈ F, ∀ j, W' e a j = W e b j) := by sorry
