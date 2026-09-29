-- Prove2me | solution 1 for mme_CW_q6_type2_cyclic_hash_mode_code_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T22:37:57.87704+00:00
-- url     : https://prove2.me/submissions/3ad25ddf-217e-4f62-9f61-ca91158fd23f

import Mathlib
import Definitions.Def_mme_CW_q6_type2_cyclic_hash_mode_code

open MME

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {p N : ℕ} [Fact p.Prime] (hp : 7 ≤ p) (i : Fin 3) :
    Function.Injective (cwQ6Type2CyclicHashModeCode p N i) := by
  have hcast : Function.Injective (fun r : Fin 3 ↦ (r.val : ZMod p)) := by
    intro r s hrs
    apply Fin.ext
    have hv := congrArg ZMod.val hrs
    have hrp : r.val < p := by omega
    have hsp : s.val < p := by omega
    simpa [ZMod.val_natCast_of_lt hrp, ZMod.val_natCast_of_lt hsp] using hv
  have hcodeNat : Function.Injective cwQ6CoupledZHashCode := by
    intro r s hrs
    fin_cases r <;> fin_cases s <;>
      simp [cwQ6CoupledZHashCode] at hrs ⊢
  have hcode : Function.Injective
      (fun r : Fin 3 ↦ (cwQ6CoupledZHashCode r : ZMod p)) := by
    intro r s hrs
    apply hcodeNat
    have hv := congrArg ZMod.val hrs
    have hrp : cwQ6CoupledZHashCode r < p := by
      fin_cases r <;> simp [cwQ6CoupledZHashCode] <;> omega
    have hsp : cwQ6CoupledZHashCode s < p := by
      fin_cases s <;> simp [cwQ6CoupledZHashCode] <;> omega
    simpa [ZMod.val_natCast_of_lt hrp, ZMod.val_natCast_of_lt hsp] using hv
  have htwo : (2 : ZMod p) ≠ 0 := by
    exact (ZMod.natCast_eq_zero_iff 2 p).not.mpr
      (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))
  have hfour : (4 : ZMod p) ≠ 0 := by
    exact (ZMod.natCast_eq_zero_iff 4 p).not.mpr
      (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))
  have hnegfour : (-4 : ZMod p) ≠ 0 := neg_ne_zero.mpr hfour
  have hscaled
      (k : ZMod p) (hk : k ≠ 0) :
      Function.Injective (fun r : Fin 3 ↦ k * (r.val : ZMod p)) := by
    intro r s hrs
    apply hcast
    exact mul_left_cancel₀ hk hrs
  have hscaledCode
      (k : ZMod p) (hk : k ≠ 0) :
      Function.Injective
        (fun r : Fin 3 ↦ k * (cwQ6CoupledZHashCode r : ZMod p)) := by
    intro r s hrs
    apply hcode
    exact mul_left_cancel₀ hk hrs
  intro u v huv
  rcases u with ⟨u0, u1, u2⟩
  rcases v with ⟨v0, v1, v2⟩
  apply Prod.ext
  · funext j
    fin_cases i
    · exact hscaled 2 htwo (congrFun (congrFun huv 0) j)
    · exact hscaled 2 htwo (congrFun (congrFun huv 0) j)
    · exact hcode (congrFun (congrFun huv 0) j)
  · apply Prod.ext
    · funext j
      fin_cases i
      · exact hscaledCode 4 hfour (congrFun (congrFun huv 1) j)
      · exact hscaled (-4) hnegfour (congrFun (congrFun huv 1) j)
      · exact hscaled 2 htwo (congrFun (congrFun huv 1) j)
    · funext j
      fin_cases i
      · exact hscaled (-4) hnegfour (congrFun (congrFun huv 2) j)
      · exact hscaledCode 4 hfour (congrFun (congrFun huv 2) j)
      · exact hscaled 2 htwo (congrFun (congrFun huv 2) j)
