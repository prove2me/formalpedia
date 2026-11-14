-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_potts_weighted_vertex_recursion
-- name    : ZeroFreeRRG.Hardcore.potts_weighted_vertex_recursion
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T08:48:53.654055+00:00
-- url     : https://prove2.me/theorems/a19ae1a3-35dd-4f3d-ae9f-d9504a21e661
-- title:
--   Fixed-color weighted Potts recursion
-- statement:
--   A weighted Potts sum with one additional unassigned vertex is the sum over all possible colors assigned to that vertex.
-- source:
--   Auxiliary step for Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, Lemma 5.7.

import Mathlib
import Definitions.Def_ZeroFreeRRG_Hardcore_PottsWeighted
import Definitions.Def_ZeroFreeRRG_Hardcore_PottsPartial
set_option autoImplicit false
open ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem ZeroFreeRRG.Hardcore.potts_weighted_vertex_recursion {V : Type} [Fintype V] (q : ℕ) (G : SimpleGraph V)
    (W : Sym2 V → Fin q → Fin q → ℂ) (hW : ∀ e i j, W e i j = W e j i) (S : Finset V) (τ : V → Fin q) (v : V) (hv : v ∉ S) :
    pottsWeightedPartial q G W hW S τ = ∑ c : Fin q, pottsWeightedPartial q G W hW (insert v S) (Function.update τ v c) := by sorry
