-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_potts_joint_induction
-- name    : ZeroFreeRRG.Hardcore.potts_joint_induction
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T09:16:45.708608+00:00
-- url     : https://prove2.me/theorems/9616704c-44bb-4ce6-9f7a-e10d82e96140
-- title:
--   Joint nonvanishing and phase induction for Potts sums
-- statement:
--   Suppose phase coherence at each fixed vertex set follows from uniform nonvanishing and phase coherence at every larger fixed set. For $d\ge3$, $q\ge2$, and $|\beta-1|<0.35/d$, descending induction then proves both properties at every fixed vertex set. The phase step is an explicit hypothesis.
-- source:
--   Auxiliary induction reduction for Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, Lemma 5.7.

import Mathlib
import Definitions.Def_ZeroFreeRRG_Hardcore_PottsInduction
set_option autoImplicit false
open MeasureTheory Set ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem ZeroFreeRRG.Hardcore.potts_joint_induction (d q : ℕ) (hd : 3 ≤ d) (hq : 2 ≤ q)
    (V : Type) [Fintype V] (G : SimpleGraph V) (β : ℂ) (hβ : ‖β-1‖ < 0.35/(d:ℝ))
    (phaseStep : ∀ S : Finset V,
      (∀ T : Finset V, S ⊂ T → pottsNonzeroAt q G β T ∧ pottsCoherentAt q G β T) →
      pottsCoherentAt q G β S) :
    ∀ S : Finset V, pottsNonzeroAt q G β S ∧ pottsCoherentAt q G β S := by sorry
