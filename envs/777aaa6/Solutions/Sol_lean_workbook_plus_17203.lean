-- Prove2me | solution 1 for lean_workbook_plus_17203
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:41:19.263647+00:00
-- url     : https://prove2.me/submissions/7a36bb92-a88d-4e66-a767-8e53bab87b9b

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution {G : Type*} [Group G] {H1 H2 : Subgroup G}
  (h1 : H1.Normal) (h2 : H2.Normal) : (H1 ⊓ H2).Normal := by
  intros
  exact Subgroup.normal_inf_normal H1 H2
