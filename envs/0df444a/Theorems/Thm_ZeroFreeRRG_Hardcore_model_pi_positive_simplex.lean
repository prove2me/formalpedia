-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_model_pi_positive_simplex
-- name    : ZeroFreeRRG.Hardcore.model_pi_positive_simplex
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T09:45:51.649897+00:00
-- url     : https://prove2.me/theorems/c152d61e-124d-44ae-bda1-0b6f2f338944
-- title:
--   Positive normalized spin marginals
-- statement:
--   For every valid hardcore or antiferromagnetic Potts model at a positive nontrivial parameter, all spin marginal probabilities are strictly positive and the spin marginal belongs to the probability simplex.
-- source:
--   Auxiliary model identity for Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, p. 39, proof of Lemma 5.6 and equation (29).

import Mathlib
import Definitions.Def_ZeroFreeRRG_Hardcore_BetheFunctional
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
open MeasureTheory ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem ZeroFreeRRG.Hardcore.model_pi_positive_simplex (m : Model) (hm : m.Valid) (t : ℝ) (ht : m.PosParam t) :
    (∀ a, 0 < m.pi t a) ∧ m.pi t ∈ stdSimplex ℝ m.Spin := by sorry
