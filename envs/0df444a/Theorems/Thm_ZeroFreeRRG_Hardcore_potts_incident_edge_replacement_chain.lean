-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_potts_incident_edge_replacement_chain
-- name    : ZeroFreeRRG.Hardcore.potts_incident_edge_replacement_chain
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T09:22:15.406621+00:00
-- url     : https://prove2.me/theorems/f938d88d-2e51-4580-b27e-bd125473279a
-- title:
--   Incident-edge replacement chain for Potts interactions
-- statement:
--   For symmetric Potts interactions lying on a common segment, one can perform exactly degree(v) successive symmetric row replacements, one per edge incident to v. Every intermediate interaction system preserves symmetry and the segment; each step changes only its selected edge and makes the selected a-row equal to the old b-row. The last system is the simultaneous replacement on all incident edges.
-- source:
--   Auxiliary step for Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, Lemma 5.7.

import Mathlib
import Definitions.Def_ZeroFreeRRG_Hardcore_PottsRowChain
set_option autoImplicit false
open MeasureTheory Set ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem ZeroFreeRRG.Hardcore.potts_incident_edge_replacement_chain {V : Type} [Fintype V] (q : ℕ) (G : SimpleGraph V) (β : ℂ)
    (W : Sym2 V → Fin q → Fin q → ℂ) (hW : ∀ e i j, W e i j = W e j i)
    (hseg : pottsSegmentWeights q G β W) (v : V) (a b : Fin q) :
    ∃ (n : ℕ) (Ws : ℕ → Sym2 V → Fin q → Fin q → ℂ),
      n = G.degree v ∧ Ws 0 = W ∧ Ws n = pottsReplaceRows W (G.incidenceFinset v) a b ∧
      (∀ k, (∀ e i j, Ws k e i j = Ws k e j i) ∧ pottsSegmentWeights q G β (Ws k)) ∧
      (∀ k < n, ∃ e ∈ G.incidenceFinset v,
        (∀ e' ≠ e, ∀ i j, Ws (k+1) e' i j = Ws k e' i j) ∧
        (∀ j, Ws (k+1) e a j = Ws k e b j)) := by sorry
