-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_potts_row_replacement_endpoint
-- name    : ZeroFreeRRG.Hardcore.potts_row_replacement_endpoint
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T09:22:17.696771+00:00
-- url     : https://prove2.me/theorems/2e7cba36-0352-4b4d-89c6-c4816fd75db3
-- title:
--   Potts restricted-sum endpoint identity
-- statement:
--   Let v be outside a prescribed vertex set S. Symmetrically replacing row a by row b on every edge incident to v makes the restricted partition sum with v pinned to a equal to the original restricted sum with v pinned to b. The identity includes arbitrary existing restrictions on S.
-- source:
--   Auxiliary step for Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, Lemma 5.7.

import Mathlib
import Definitions.Def_ZeroFreeRRG_Hardcore_PottsRowChain
set_option autoImplicit false
open MeasureTheory Set ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem ZeroFreeRRG.Hardcore.potts_row_replacement_endpoint {V : Type} [Fintype V] (q : ℕ) (G : SimpleGraph V)
    (W : Sym2 V → Fin q → Fin q → ℂ) (hW : ∀ e i j, W e i j = W e j i)
    (S : Finset V) (τ : V → Fin q) (v : V) (hv : v ∉ S) (a b : Fin q)
    (hW' : ∀ e i j, pottsReplaceRows W (G.incidenceFinset v) a b e i j =
      pottsReplaceRows W (G.incidenceFinset v) a b e j i) :
    pottsWeightedPartial q G (pottsReplaceRows W (G.incidenceFinset v) a b) hW'
      (insert v S) (Function.update τ v a) =
    pottsWeightedPartial q G W hW (insert v S) (Function.update τ v b) := by sorry
