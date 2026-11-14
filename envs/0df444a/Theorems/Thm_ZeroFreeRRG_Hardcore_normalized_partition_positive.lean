-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_normalized_partition_positive
-- name    : ZeroFreeRRG.Hardcore.normalized_partition_positive
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:04:59.49704+00:00
-- url     : https://prove2.me/theorems/50cd4919-c12f-4b42-9893-74cae4e60b4d
-- title:
--   Positive normalized partition function on every multigraph
-- statement:
--   For every valid hardcore or Potts model at a positive nontrivial parameter and every configuration-model matching, the normalized partition function is strictly positive, including when the multigraph has loops or parallel edges.
-- source:
--   Auxiliary probabilistic identity for Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, §4.3 and p. 39, proof of Lemma 5.6.

import Mathlib
import Definitions.Def_ZeroFreeRRG_Hardcore_Moments
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
open Set Filter MeasureTheory AFIsingKS ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem ZeroFreeRRG.Hardcore.normalized_partition_positive (m : Model) (hm : m.Valid) (t : ℝ) (ht : m.PosParam t)
    (d n : ℕ) (M : Matching n d) : 0 < normZ m t M := by sorry
