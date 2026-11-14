-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_potts_edge_free_replacement
-- name    : ZeroFreeRRG.Hardcore.potts_edge_free_replacement
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T09:14:29.331195+00:00
-- url     : https://prove2.me/theorems/635bd756-7071-48dc-af1e-e9d07655b0b2
-- title:
--   One-edge Potts replacement with a free neighbor
-- statement:
--   Fix the color of one endpoint $v$ of an edge $\{v,u\}$, leaving $u$ unassigned. If two symmetric edge-interaction systems agree away from that edge and the old edge coefficients are nonzero, then the new restricted partition sum equals the sum, over colors $c$ of $u$, of the old restricted sum with $u=c$ multiplied by the ratio of the new and old edge coefficients.
-- source:
--   Supporting identity for Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, Lemma 5.7.

import Mathlib
import Definitions.Def_ZeroFreeRRG_Hardcore_PottsWeighted
set_option autoImplicit false
open ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem ZeroFreeRRG.Hardcore.potts_edge_free_replacement {V : Type} [Fintype V] (q : ℕ) (G : SimpleGraph V)
    (W W' : Sym2 V → Fin q → Fin q → ℂ)
    (hW : ∀ e i j, W e i j = W e j i) (hW' : ∀ e i j, W' e i j = W' e j i)
    (S : Finset V) (τ : V → Fin q) (v u : V) (hv : v ∈ S) (hu : u ∉ S)
    (he : s(v,u) ∈ G.edgeFinset)
    (hother : ∀ e ≠ s(v,u), ∀ i j, W' e i j = W e i j)
    (hnz : ∀ c : Fin q, W s(v,u) (τ v) c ≠ 0) :
    pottsWeightedPartial q G W' hW' S τ =
      ∑ c : Fin q, (W' s(v,u) (τ v) c / W s(v,u) (τ v) c) *
        pottsWeightedPartial q G W hW (insert u S) (Function.update τ u c) := by sorry
