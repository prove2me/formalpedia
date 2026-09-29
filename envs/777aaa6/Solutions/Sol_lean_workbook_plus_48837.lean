-- Prove2me | solution 1 for lean_workbook_plus_48837
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T01:16:57.412465+00:00
-- url     : https://prove2.me/submissions/7522edcf-3032-4745-b580-6ae7ff0ad3d1

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

set_option maxHeartbeats 200000 in
theorem solution : (Finset.filter (λ x => x % 4 = 0) (Finset.range 22)).card = 6 ∧ (Finset.filter (λ x => x % 4 = 1) (Finset.range 22)).card = 6 ∧ (Finset.filter (λ x => x % 4 = 2) (Finset.range 22)).card = 5 ∧ (Finset.filter (λ x => x % 4 = 3) (Finset.range 22)).card = 5 := by
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
