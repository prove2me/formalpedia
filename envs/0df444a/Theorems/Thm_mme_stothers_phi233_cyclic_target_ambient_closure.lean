-- Prove2me | Theorems.Thm_mme_stothers_phi233_cyclic_target_ambient_closure
-- name    : mme_stothers_phi233_cyclic_target_ambient_closure
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T22:42:23.444471+00:00
-- url     : https://prove2.me/theorems/c97306e6-6d8e-4dc5-8a41-0a8a32678733
-- title:
--   The phi_233 cyclic finsets satisfy the type-2 closure interface
-- statement:
--   The concrete exact-profile cyclic target is contained in the full same-marginal cyclic ambient family. Moreover, whenever three target edges have a coordinatewise-supported cyclic mixture, the ambient family contains an edge with mode-zero vertex from the first edge, mode-one vertex from the second, and mode-two vertex from the third. This is exactly the static closure hypothesis of the generic type-2 collision-budget and tensor-isolation theorems.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), cyclic symmetrization and the same-marginal completion argument in Lemma 3.3 and Section 5, pp. 356--360 and 365--366, https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi233_cyclic_finsets

open MME

set_option autoImplicit false

theorem mme_stothers_phi233_cyclic_target_ambient_closure
    (N alpha beta gamma delta : ℕ) :
    MME.StothersFourth.Phi233.targetFinset
        N alpha beta gamma delta ⊆
      MME.StothersFourth.Phi233.ambientFinset
        N alpha beta gamma delta ∧
    ∀ x ∈ MME.StothersFourth.Phi233.targetFinset
          N alpha beta gamma delta,
      ∀ y ∈ MME.StothersFourth.Phi233.targetFinset
          N alpha beta gamma delta,
        ∀ z ∈ MME.StothersFourth.Phi233.targetFinset
            N alpha beta gamma delta,
          MME.StothersFourth.Phi233.CyclicCoordinatewiseSupported x y z →
            ∃ e ∈ MME.StothersFourth.Phi233.ambientFinset
                N alpha beta gamma delta,
              MME.StothersFourth.Phi233.cyclicModeWord e 0 =
                  MME.StothersFourth.Phi233.cyclicModeWord x 0 ∧
              MME.StothersFourth.Phi233.cyclicModeWord e 1 =
                  MME.StothersFourth.Phi233.cyclicModeWord y 1 ∧
              MME.StothersFourth.Phi233.cyclicModeWord e 2 =
                  MME.StothersFourth.Phi233.cyclicModeWord z 2 := by
  sorry
