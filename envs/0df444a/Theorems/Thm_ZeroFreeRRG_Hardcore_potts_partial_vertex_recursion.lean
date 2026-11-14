-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_potts_partial_vertex_recursion
-- name    : ZeroFreeRRG.Hardcore.potts_partial_vertex_recursion
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T08:44:37.630381+00:00
-- url     : https://prove2.me/theorems/d8f796a0-fb38-44b8-b93e-df14e99004f0
-- title:
--   Fixed-color Potts partition recursion
-- statement:
--   For a vertex outside the fixed set, the restricted Potts partition sum is the sum of the restricted sums obtained by assigning each possible color to that vertex.
-- source:
--   Auxiliary step for Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, Lemma 5.7.

import Mathlib
import Definitions.Def_ZeroFreeRRG_Hardcore_PottsPartial
set_option autoImplicit false
open ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem ZeroFreeRRG.Hardcore.potts_partial_vertex_recursion {V : Type} [Fintype V] (q : ℕ) (G : SimpleGraph V)
    (β : ℂ) (S : Finset V) (τ : V → Fin q) (v : V) (hv : v ∉ S) :
    pottsPartialZ q G β S τ = ∑ c : Fin q, pottsPartialZ q G β (insert v S) (Function.update τ v c) := by sorry
