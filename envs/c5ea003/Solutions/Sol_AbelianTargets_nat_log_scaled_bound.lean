-- Prove2me | solution 1 for AbelianTargets.nat_log_scaled_bound
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-19T04:12:38.546557+00:00
-- url     : https://prove2.me/submissions/74b7b2e2-7622-408b-afe1-fbd6bba70ac0

import Definitions.Def_AT260939824_NaturalLogScaleBounds
import Init
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

set_option autoImplicit false

-- Preserved source skeleton: AbelianTargets.NaturalLogScaleBounds
section
/-! Converting the literal base-`m` carrier height into the analytic scale bound. -/
namespace AbelianTargets
open Filter Topology
noncomputable section

theorem nat_log_le_real_log (m : ℕ) (hm : 2≤m) (R : ℕ) (hR : 0<R) :
    (Nat.log m R : ℝ)≤Real.log (R : ℝ)/Real.log (m : ℝ) := by
  have hm' : (1 : ℝ)<m := by exact_mod_cast (show 1<m by omega)
  have hp : 0<(m : ℝ)^Nat.log m R := pow_pos (by linarith) _
  have hpow : (m : ℝ)^Nat.log m R≤(R : ℝ) := by
    exact_mod_cast Nat.pow_log_le_self m (Nat.ne_of_gt hR)
  have hh := Real.log_le_log hp hpow
  rw [Real.log_pow] at hh
  exact (le_div_iff₀ (Real.log_pos hm')).mpr hh







end
end AbelianTargets

end

/-! Converting the literal base-`m` carrier height into the analytic scale bound. -/
namespace AbelianTargets
end AbelianTargets
open AbelianTargets
open Filter Topology

theorem solution (m : ℕ) (hm : 2≤m) (C : ℕ) (hC : 1≤C) (L : ℕ) :
    (Nat.log m (C*(L+2))+1 : ℝ)≤carrierHeightLogCoefficient m C*Real.log ((L : ℝ)+2) := by
  have hCpos : 0<(C : ℝ) := by exact_mod_cast (show 0<C by omega)
  have hCm : 1≤(C : ℝ) := by exact_mod_cast hC
  have hmlog : 0<Real.log (m : ℝ) := Real.log_pos (by exact_mod_cast (show 1<m by omega))
  have htwo : 0<Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hx : 0<(L : ℝ)+2 := by positivity
  have hlogx : Real.log 2≤Real.log ((L : ℝ)+2) := Real.log_le_log (by norm_num) (by have := Nat.cast_nonneg (α := ℝ) L; linarith)
  have hlogC : 0≤Real.log (C : ℝ) := Real.log_nonneg hCm
  have hratio : 1≤Real.log ((L : ℝ)+2)/Real.log 2 := (one_le_div htwo).mpr hlogx
  have hCscale : Real.log (C : ℝ)≤(Real.log (C : ℝ)/Real.log 2)*Real.log ((L : ℝ)+2) := by
    have hh := mul_le_mul_of_nonneg_left hratio hlogC
    calc
      Real.log (C : ℝ)≤Real.log (C : ℝ)*(Real.log ((L : ℝ)+2)/Real.log 2) := by simpa using hh
      _ = _ := by ring
  have hn := nat_log_le_real_log m hm (C*(L+2)) (by positivity)
  have he : ((C*(L+2) : ℕ) : ℝ)=(C : ℝ)*((L : ℝ)+2) := by push_cast; rfl
  rw [he,Real.log_mul hCpos.ne' hx.ne'] at hn
  have hlogbound : (Real.log (C : ℝ)+Real.log ((L : ℝ)+2))/Real.log (m : ℝ)≤
      ((1+Real.log (C : ℝ)/Real.log 2)/Real.log (m : ℝ))*Real.log ((L : ℝ)+2) := by
    apply (div_le_iff₀ hmlog).mpr
    have he' : (((1+Real.log (C : ℝ)/Real.log 2)/Real.log (m : ℝ))*Real.log ((L : ℝ)+2))*Real.log (m : ℝ)=
        (1+Real.log (C : ℝ)/Real.log 2)*Real.log ((L : ℝ)+2) := by field_simp
    rw [he']; nlinarith
  have hone : (1 : ℝ)≤(1/Real.log 2)*Real.log ((L : ℝ)+2) := by
    convert hratio using 1 <;> ring
  dsimp [carrierHeightLogCoefficient]
  calc
    _ ≤ ((1+Real.log (C : ℝ)/Real.log 2)/Real.log (m : ℝ))*Real.log ((L : ℝ)+2)+
        (1/Real.log 2)*Real.log ((L : ℝ)+2) := add_le_add (hn.trans hlogbound) hone
    _ = _ := by ring
