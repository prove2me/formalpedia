-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_model_edge_nonnegative
-- name    : ZeroFreeRRG.Hardcore.model_edge_nonnegative
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:01:09.221168+00:00
-- url     : https://prove2.me/theorems/6e796039-03e5-4dbb-91d1-05fd82bfbe16
-- title:
--   Nonnegative edge marginals at positive parameters
-- statement:
--   For each valid hardcore or Potts model at a positive nontrivial parameter, every entry of the canonical edge-marginal matrix is nonnegative.
-- source:
--   Auxiliary probabilistic step for Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, p. 39, proof of Lemma 5.6.

import Mathlib
import Definitions.Def_ZeroFreeRRG_Hardcore_Moments
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
open Set Filter MeasureTheory AFIsingKS ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem ZeroFreeRRG.Hardcore.model_edge_nonnegative (m : Model) (hm : m.Valid) (t : ℝ) (ht : m.PosParam t) :
    ∀ a b, 0 ≤ m.P t a b := by sorry
