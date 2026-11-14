-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_potts_weighted_specialization
-- name    : ZeroFreeRRG.Hardcore.potts_weighted_specialization
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T08:48:59.31134+00:00
-- url     : https://prove2.me/theorems/e5aa4196-bf8f-4dad-ab68-8c6bc12007f4
-- title:
--   Weighted Potts sum specializes to the usual Potts sum
-- statement:
--   When each interaction equals $\beta$ on equal colors and $1$ otherwise, the weighted restricted partition sum is the ordinary restricted Potts sum.
-- source:
--   Auxiliary step for Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, Lemma 5.7.

import Mathlib
import Definitions.Def_ZeroFreeRRG_Hardcore_PottsWeighted
import Definitions.Def_ZeroFreeRRG_Hardcore_PottsPartial
set_option autoImplicit false
open ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem ZeroFreeRRG.Hardcore.potts_weighted_specialization {V : Type} [Fintype V] (q : ℕ) (G : SimpleGraph V)
    (β : ℂ) (S : Finset V) (τ : V → Fin q) :
    let W := fun (_ : Sym2 V) (i j : Fin q) => if i=j then β else 1
    let hW : ∀ e i j, W e i j = W e j i := by intro e i j; simp [W,eq_comm]
    pottsWeightedPartial q G W hW S τ = pottsPartialZ q G β S τ := by sorry
