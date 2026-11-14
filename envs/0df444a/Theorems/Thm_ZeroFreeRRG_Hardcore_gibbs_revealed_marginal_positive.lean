-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_gibbs_revealed_marginal_positive
-- name    : ZeroFreeRRG.Hardcore.gibbs_revealed_marginal_positive
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:11:32.585192+00:00
-- url     : https://prove2.me/theorems/12448f6d-96e9-40f1-867b-10b96a0fbd59
-- title:
--   Positive configurations have positive revealed marginals
-- statement:
--   When all Gibbs weights are nonnegative, every spin configuration with positive Gibbs weight has a strictly positive Gibbs marginal on every reveal set.
-- source:
--   Auxiliary revealed-density identity in Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, pp. 39–40, proof of Lemma 5.6.

import Mathlib
import Definitions.Def_ZeroFreeRRG_Hardcore_Moments
set_option autoImplicit false
open Set Filter MeasureTheory AFIsingKS ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem ZeroFreeRRG.Hardcore.gibbs_revealed_marginal_positive (m : Model) (t : ℝ) (d n : ℕ) (M : Matching n d)
    (σ : Fin n → m.Spin) (U : Finset (Fin n))
    (hnonneg : ∀ σ', 0 ≤ gibbs m t M σ') (hσ : 0 < gibbs m t M σ) :
    0 < gibbsMarg m t M σ U := by sorry
