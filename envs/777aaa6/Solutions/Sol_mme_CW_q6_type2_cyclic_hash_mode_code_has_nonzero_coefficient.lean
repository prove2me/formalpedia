-- Prove2me | solution 1 for mme_CW_q6_type2_cyclic_hash_mode_code_has_nonzero_coefficient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T22:44:42.320509+00:00
-- url     : https://prove2.me/submissions/042ff3bc-706f-41a8-904b-efed1fd9acb0

import Mathlib
import Definitions.Def_mme_CW_q6_type2_cyclic_hash_mode_code

open MME

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {p N L G : ℕ} [Fact p.Prime] (hp : 7 ≤ p) (hN : 0 < N)
    (e : CWQ6Type2CyclicEdge N L G) (i : Fin 3) :
    ∃ r : Fin 3, ∃ j : Fin (2 * N),
      cwQ6Type2CyclicHashModeCode p N i
        (cwQ6Type2CyclicModeWord e i) r j ≠ 0 := by
  have htwo : (2 : ZMod p) ≠ 0 := by
    exact (ZMod.natCast_eq_zero_iff 2 p).not.mpr
      (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))
  fin_cases i
  · have hcard := e.1.2.2 (0 : Fin 3) (1 : Fin 3)
    have hpos : 0 < ((Finset.univ : Finset (Fin (2 * N))).filter
        (fun j ↦ e.1.1 0 j = 1)).card := by
      rw [hcard]
      simpa [cwQ6CoupledMarginalMultiplicity] using hN
    obtain ⟨j, hj⟩ := Finset.card_pos.mp hpos
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    refine ⟨0, j, ?_⟩
    simpa [cwQ6Type2CyclicHashModeCode, cwQ6Type2CyclicModeWord, hj]
      using htwo
  · have hcard := e.1.2.2 (1 : Fin 3) (1 : Fin 3)
    have hpos : 0 < ((Finset.univ : Finset (Fin (2 * N))).filter
        (fun j ↦ e.1.1 1 j = 1)).card := by
      rw [hcard]
      simpa [cwQ6CoupledMarginalMultiplicity] using hN
    obtain ⟨j, hj⟩ := Finset.card_pos.mp hpos
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    refine ⟨0, j, ?_⟩
    simpa [cwQ6Type2CyclicHashModeCode, cwQ6Type2CyclicModeWord, hj]
      using htwo
  · have hcard := e.2.1.2.2 (1 : Fin 3) (1 : Fin 3)
    have hpos : 0 < ((Finset.univ : Finset (Fin (2 * N))).filter
        (fun j ↦ e.2.1.1 1 j = 1)).card := by
      rw [hcard]
      simpa [cwQ6CoupledMarginalMultiplicity] using hN
    obtain ⟨j, hj⟩ := Finset.card_pos.mp hpos
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    refine ⟨1, j, ?_⟩
    simpa [cwQ6Type2CyclicHashModeCode, cwQ6Type2CyclicModeWord, hj]
      using htwo
