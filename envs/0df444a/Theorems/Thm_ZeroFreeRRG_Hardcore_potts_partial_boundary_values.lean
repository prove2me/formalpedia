-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_potts_partial_boundary_values
-- name    : ZeroFreeRRG.Hardcore.potts_partial_boundary_values
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T08:44:28.405364+00:00
-- url     : https://prove2.me/theorems/82ad79fe-3b8c-46db-8448-f112021bf724
-- title:
--   Boundary values for restricted Potts sums
-- statement:
--   The Potts sum with no fixed vertices is the full partition function; fixing every vertex leaves exactly the weight of the prescribed coloring.
-- source:
--   Auxiliary step for Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, Lemma 5.7.

import Mathlib
import Definitions.Def_ZeroFreeRRG_Hardcore_PottsPartial
set_option autoImplicit false
open ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem ZeroFreeRRG.Hardcore.potts_partial_boundary_values {V : Type} [Fintype V] (q : ℕ) (G : SimpleGraph V)
    (β : ℂ) (τ : V → Fin q) :
    pottsPartialZ q G β ∅ τ = pottsZ q G β ∧
    pottsPartialZ q G β Finset.univ τ = β ^ monoEdges G τ := by sorry
