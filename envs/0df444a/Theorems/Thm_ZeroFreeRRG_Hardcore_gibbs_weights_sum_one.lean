-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_gibbs_weights_sum_one
-- name    : ZeroFreeRRG.Hardcore.gibbs_weights_sum_one
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:05:37.811682+00:00
-- url     : https://prove2.me/theorems/b75674e8-d554-4cc5-98af-50abcb8924a4
-- title:
--   Gibbs weights sum to one on each configuration multigraph
-- statement:
--   For every configuration-model matching and either valid model at a positive nontrivial parameter, the Gibbs weights over all spin assignments sum to one.
-- source:
--   Auxiliary probabilistic identity in Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, §4.3 and p. 39, proof of Lemma 5.6.

import Mathlib
import Definitions.Def_ZeroFreeRRG_Hardcore_Moments
set_option autoImplicit false
open Set Filter MeasureTheory AFIsingKS ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem ZeroFreeRRG.Hardcore.gibbs_weights_sum_one (m : Model) (hm : m.Valid) (t : ℝ) (ht : m.PosParam t)
    (d n : ℕ) (M : Matching n d) :
    (∑ σ : Fin n → m.Spin, gibbs m t M σ) = 1 := by sorry
