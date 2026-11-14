-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_planted_graph_conditional_gibbs
-- name    : ZeroFreeRRG.Hardcore.planted_graph_conditional_gibbs
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:18:26.329655+00:00
-- url     : https://prove2.me/theorems/b282640a-0ac0-4652-bace-89444b1ff27f
-- title:
--   Gibbs conditional law under the planted graph marginal
-- statement:
--   For a valid positive-parameter model, the planted weight of a graph and spin assignment equals the planted graph-marginal weight times the Gibbs probability of that spin assignment.
-- source:
--   Auxiliary planted-law identity in Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, §4.3 and pp. 39–40, proof of Lemma 5.6.

import Mathlib
import Definitions.Def_ZeroFreeRRG_Hardcore_Moments
set_option autoImplicit false
open Set Filter MeasureTheory AFIsingKS ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem ZeroFreeRRG.Hardcore.planted_graph_conditional_gibbs (m : Model) (hm : m.Valid) (t : ℝ) (ht : m.PosParam t)
    (d n : ℕ) (M : Matching n d) (σ : Fin n → m.Spin) :
    planted m t M σ = (∑ τ : Fin n → m.Spin, planted m t M τ) * gibbs m t M σ := by sorry
