-- Prove2me | solution 1 for lean_workbook_plus_9464
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T01:17:27.411863+00:00
-- url     : https://prove2.me/submissions/d06f4f84-41f0-4be7-afca-66bd453bb296

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

set_option maxHeartbeats 200000 in
theorem solution :
  1 / 2 + (2 - Real.sqrt 2) / 2 = (3 - Real.sqrt 2) / 2 := by
  first
    | (trace "TAC:norm_num"; norm_num; done)
    | (trace "TAC:decide"; decide; done)
    | (trace "TAC:rfl"; rfl; done)
    | (trace "TAC:simp"; simp; done)
    | (trace "TAC:norm_num_intros"; (intros; norm_num); done)
    | (trace "TAC:simp_intros"; (intros; simp); done)
    | (trace "TAC:simp_all"; (intros; simp_all); done)
    | (trace "TAC:positivity"; (intros; positivity); done)
    | (trace "TAC:omega"; (intros; omega); done)
    | (trace "TAC:linarith"; (intros; linarith); done)
    | (trace "TAC:ring"; (intros; ring); done)
    | (trace "TAC:field_simp_ring"; (intros; field_simp; ring); done)
    | (trace "TAC:norm_num_factorial"; (intros; norm_num [Nat.factorial, Nat.choose]); done)
    | (trace "TAC:norm_num_mod"; (intros; norm_num [Nat.pow_mod, Nat.add_mod, Nat.mul_mod, Int.emod_emod_of_dvd]); done)
    | (trace "TAC:constructor_norm_num"; (intros; constructor <;> norm_num); done)
    | (trace "TAC:norm_num_ring_nf"; (intros; norm_num; ring_nf); done)
    | (trace "TAC:simp_ring"; (intros; simp; ring); done)
    | (trace "TAC:decide_intros"; (intros; decide); done)
    | (trace "TAC:nlinarith"; (intros; nlinarith); done)
