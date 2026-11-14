-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_potts_edge_fixed_replacement
-- name    : ZeroFreeRRG.Hardcore.potts_edge_fixed_replacement
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T09:15:56.419621+00:00
-- url     : https://prove2.me/theorems/296ef488-ddc0-4fa0-be4f-acf5394b7704
-- title:
--   One-edge Potts replacement with both endpoints fixed
-- statement:
--   If two symmetric interaction systems agree away from an edge whose endpoints have prescribed colors, and the old edge coefficient is nonzero, the new restricted Potts sum equals the old one multiplied by the new-to-old coefficient ratio.
-- source:
--   Supporting step for Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, Lemma 5.7.

import Mathlib
import Definitions.Def_ZeroFreeRRG_Hardcore_PottsSegment
set_option autoImplicit false
open MeasureTheory Set ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem ZeroFreeRRG.Hardcore.potts_edge_fixed_replacement {V : Type} [Fintype V] (q : ℕ) (G : SimpleGraph V)
    (W W' : Sym2 V → Fin q → Fin q → ℂ)
    (hW : ∀ e i j, W e i j = W e j i) (hW' : ∀ e i j, W' e i j = W' e j i)
    (S : Finset V) (τ : V → Fin q) (v u : V) (hv : v ∈ S) (hu : u ∈ S)
    (he : s(v,u) ∈ G.edgeFinset)
    (hother : ∀ e ≠ s(v,u), ∀ i j, W' e i j = W e i j)
    (hnz : W s(v,u) (τ v) (τ u) ≠ 0) :
    pottsWeightedPartial q G W' hW' S τ =
      (W' s(v,u) (τ v) (τ u) / W s(v,u) (τ v) (τ u)) *
        pottsWeightedPartial q G W hW S τ := by sorry
