-- Prove2me | solution 1 for mme_stothers_phi125_cyclic_hash_mode_code_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-03T00:24:35.422042+00:00
-- url     : https://prove2.me/submissions/db151140-a2f0-4395-9361-46ffdfa4d56a

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi125_cyclic_hash_data

open MME.StothersFourth.Phi125

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {p N : ℕ} [Fact p.Prime] (hp : 5 ≤ p) (i : Fin 3) :
    Function.Injective (cyclicHashModeCode p N i) := by
  have hcast : Function.Injective
      (fun r : Fin 5 ↦ (r.val : ZMod p)) := by
    intro r s hrs
    apply Fin.ext
    have hv := congrArg ZMod.val hrs
    have hrp : r.val < p := by omega
    have hsp : s.val < p := by omega
    simpa [ZMod.val_natCast_of_lt hrp,
      ZMod.val_natCast_of_lt hsp] using hv
  have hcomp : Function.Injective
      (fun r : Fin 5 ↦ (4 : ZMod p) - (r.val : ZMod p)) := by
    intro r s hrs
    apply hcast
    have hneg : -(r.val : ZMod p) = -(s.val : ZMod p) := by
      linear_combination hrs
    exact neg_inj.mp hneg
  have htwo : (2 : ZMod p) ≠ 0 := by
    exact (ZMod.natCast_eq_zero_iff 2 p).not.mpr
      (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))
  have hfour : (4 : ZMod p) ≠ 0 := by
    exact (ZMod.natCast_eq_zero_iff 4 p).not.mpr
      (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))
  have hscaledCast (k : ZMod p) (hk : k ≠ 0) :
      Function.Injective (fun r : Fin 5 ↦ k * (r.val : ZMod p)) := by
    intro r s hrs
    apply hcast
    exact mul_left_cancel₀ hk hrs
  have hscaledComp (k : ZMod p) (hk : k ≠ 0) :
      Function.Injective
        (fun r : Fin 5 ↦ k * ((4 : ZMod p) - (r.val : ZMod p))) := by
    intro r s hrs
    apply hcomp
    exact mul_left_cancel₀ hk hrs
  intro u v huv
  rcases u with ⟨u0, u1, u2⟩
  rcases v with ⟨v0, v1, v2⟩
  apply Prod.ext
  · funext j
    fin_cases i
    · apply hscaledCast 2 htwo
      simpa [cyclicHashModeCode,
        MME.StothersFourth.Phi233.cyclicHashModeCode] using
          congrFun (congrFun huv 0) j
    · apply hscaledCast 2 htwo
      simpa [cyclicHashModeCode,
        MME.StothersFourth.Phi233.cyclicHashModeCode] using
          congrFun (congrFun huv 0) j
    · apply hcomp
      simpa [cyclicHashModeCode,
        MME.StothersFourth.Phi233.cyclicHashModeCode] using
          congrFun (congrFun huv 0) j
  · apply Prod.ext
    · funext j
      fin_cases i
      · apply hscaledComp 4 hfour
        simpa [cyclicHashModeCode,
          MME.StothersFourth.Phi233.cyclicHashModeCode] using
            congrFun (congrFun huv 1) j
      · apply hcast
        simpa [cyclicHashModeCode,
          MME.StothersFourth.Phi233.cyclicHashModeCode, htwo] using
            congrFun (congrFun huv 1) j
      · apply hscaledCast 2 htwo
        simpa [cyclicHashModeCode,
          MME.StothersFourth.Phi233.cyclicHashModeCode] using
            congrFun (congrFun huv 1) j
    · funext j
      fin_cases i
      · apply hcast
        simpa [cyclicHashModeCode,
          MME.StothersFourth.Phi233.cyclicHashModeCode, htwo] using
            congrFun (congrFun huv 2) j
      · apply hscaledComp 4 hfour
        simpa [cyclicHashModeCode,
          MME.StothersFourth.Phi233.cyclicHashModeCode] using
            congrFun (congrFun huv 2) j
      · apply hscaledCast 2 htwo
        simpa [cyclicHashModeCode,
          MME.StothersFourth.Phi233.cyclicHashModeCode] using
            congrFun (congrFun huv 2) j
