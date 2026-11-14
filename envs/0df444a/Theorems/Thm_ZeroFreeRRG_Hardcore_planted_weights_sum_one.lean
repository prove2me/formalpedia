-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_planted_weights_sum_one
-- name    : ZeroFreeRRG.Hardcore.planted_weights_sum_one
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:18:30.230114+00:00
-- url     : https://prove2.me/theorems/3d508668-cdb1-41ec-891c-61b6e45255e0
-- title:
--   The planted weights sum to one
-- statement:
--   For a valid positive-parameter model whenever the matching space is nonempty, the planted weights over all matchings and spin assignments sum to one.
-- source:
--   Auxiliary planted-law identity in Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, §4.3 and pp. 39–40, proof of Lemma 5.6.

import Mathlib
import Definitions.Def_ZeroFreeRRG_Hardcore_Moments
set_option autoImplicit false
open Set Filter MeasureTheory AFIsingKS ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem ZeroFreeRRG.Hardcore.planted_weights_sum_one (m : Model) (hm : m.Valid) (t : ℝ) (ht : m.PosParam t) (d n : ℕ)
    [Nonempty (Matching n d)] :
    (∑ M : Matching n d, ∑ σ : Fin n → m.Spin, planted m t M σ) = 1 := by sorry
