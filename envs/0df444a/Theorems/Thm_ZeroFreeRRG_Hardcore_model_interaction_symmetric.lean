-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_model_interaction_symmetric
-- name    : ZeroFreeRRG.Hardcore.model_interaction_symmetric
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T11:04:17.995193+00:00
-- url     : https://prove2.me/theorems/3efb50ce-b0ce-4ce8-a023-e580f6f25566
-- title:
--   Symmetry of the model interaction
-- statement:
--   For either model at every real parameter, the normalized edge-interaction matrix is symmetric.
-- source:
--   Auxiliary support fact for Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, Appendix E.3, Step 1, p. 77.

import Mathlib
import Definitions.Def_ZeroFreeRRG_Hardcore_ConfigModel
import Definitions.Def_ZeroFreeRRG_Hardcore_BetheFunctional
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
open Set Filter MeasureTheory AFIsingKS ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem ZeroFreeRRG.Hardcore.model_interaction_symmetric (m : Model) (t : ℝ) : ∀ a b, m.M t a b = m.M t b a := by sorry
