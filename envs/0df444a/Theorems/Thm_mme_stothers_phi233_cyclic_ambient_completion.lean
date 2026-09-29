-- Prove2me | Theorems.Thm_mme_stothers_phi233_cyclic_ambient_completion
-- name    : mme_stothers_phi233_cyclic_ambient_completion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T22:36:45.3648+00:00
-- url     : https://prove2.me/theorems/c5bb58c1-17da-4c00-a1cb-8f1f513b6bd0
-- title:
--   Vertex closure of the cyclic phi_233 same-marginal ambient family
-- statement:
--   Let $x,y,z$ be three cyclic ambient $\varphi_{233}$ edges, each built from supported length-$2N$ words with the same prescribed mode marginals. If the three modewise mixtures are coordinatewise supported, then there is another ambient edge $e$ whose first cyclic vertex equals that of $x$, whose second cyclic vertex equals that of $y$, and whose third cyclic vertex equals that of $z$.
--
--   This is the exact vertex-closure property required by the generic type-2 collision-pruning theorem. It remains valid even though the $\varphi_{233}$ joint profile is not determined by its marginals.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Lemma 3.3 and the exceptional same-marginal construction in Lemma 5.1(v), pp. 356--360 and 365--366, https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi233_cyclic_ambient_data

open MME

set_option autoImplicit false

theorem mme_stothers_phi233_cyclic_ambient_completion
    {N alpha beta gamma delta : ℕ}
    (x y z : MME.StothersFourth.Phi233.CyclicAmbientEdge
      N alpha beta gamma delta)
    (hsupport :
      MME.StothersFourth.Phi233.CyclicCoordinatewiseSupported x y z) :
    ∃ e : MME.StothersFourth.Phi233.CyclicAmbientEdge
        N alpha beta gamma delta,
      MME.StothersFourth.Phi233.cyclicModeWord e 0 =
          MME.StothersFourth.Phi233.cyclicModeWord x 0 ∧
      MME.StothersFourth.Phi233.cyclicModeWord e 1 =
          MME.StothersFourth.Phi233.cyclicModeWord y 1 ∧
      MME.StothersFourth.Phi233.cyclicModeWord e 2 =
          MME.StothersFourth.Phi233.cyclicModeWord z 2 := by
  sorry
