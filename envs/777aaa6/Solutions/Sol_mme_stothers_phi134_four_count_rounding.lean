-- Prove2me | solution 1 for mme_stothers_phi134_four_count_rounding
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-05T09:50:44.185756+00:00
-- url     : https://prove2.me/submissions/b26e3e3e-dd69-45cd-add3-72fb581db72a

import Mathlib.Analysis.SpecificLimits.Basic

open Filter

set_option autoImplicit false
set_option warningAsError true

namespace MME.StothersFourth.Phi134Rounding

private noncomputable def A (a : ℝ) (n : ℕ) : ℕ :=
  ⌊a * (n : ℝ)⌋₊

private noncomputable def C (c : ℝ) (n : ℕ) : ℕ :=
  ⌊c * (n : ℝ)⌋₊

private noncomputable def S (sigma : ℝ) (n : ℕ) : ℕ :=
  ⌊sigma * (n : ℝ)⌋₊

/-- The omitted profile weight `beta = sigma-c`, rounded by subtraction so
it is compatible with the rounded sum `S`. -/
private noncomputable def B (sigma c : ℝ) (n : ℕ) : ℕ :=
  S sigma n - C c n

/-- The omitted profile weight `delta = 1-sigma-a`, used as the exact
remainder so all four integer counts sum to `n`. -/
private noncomputable def D (sigma a : ℝ) (n : ℕ) : ℕ :=
  n - (S sigma n + A a n)

private theorem C_le_S
    (sigma c : ℝ) (hcs : c ≤ sigma) (n : ℕ) :
    C c n ≤ S sigma n := by
  unfold C S
  apply Nat.floor_mono
  exact mul_le_mul_of_nonneg_right hcs (Nat.cast_nonneg n)

private theorem SA_le
    (sigma a : ℝ) (hsigma : 0 ≤ sigma) (ha : 0 ≤ a)
    (hsa : sigma + a ≤ 1) (n : ℕ) :
    S sigma n + A a n ≤ n := by
  have hS : ((S sigma n : ℕ) : ℝ) ≤ sigma * (n : ℝ) := by
    exact Nat.floor_le (mul_nonneg hsigma (Nat.cast_nonneg n))
  have hA : ((A a n : ℕ) : ℝ) ≤ a * (n : ℝ) := by
    exact Nat.floor_le (mul_nonneg ha (Nat.cast_nonneg n))
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hreal : (((S sigma n + A a n : ℕ) : ℝ)) ≤ (n : ℝ) := by
    push_cast
    calc
      (S sigma n : ℝ) + (A a n : ℝ) ≤
          sigma * (n : ℝ) + a * (n : ℝ) := add_le_add hS hA
      _ = (sigma + a) * (n : ℝ) := by ring
      _ ≤ 1 * (n : ℝ) := mul_le_mul_of_nonneg_right hsa hn
      _ = (n : ℝ) := one_mul _
  exact_mod_cast hreal

private theorem exact_sum
    (sigma a c : ℝ) (hsigma : 0 ≤ sigma) (ha : 0 ≤ a)
    (hcs : c ≤ sigma) (hsa : sigma + a ≤ 1) (n : ℕ) :
    A a n + B sigma c n + C c n + D sigma a n = n := by
  have hCS := C_le_S sigma c hcs n
  have hSA := SA_le sigma a hsigma ha hsa n
  unfold B D
  omega

private theorem tendsto_A (a : ℝ) (ha : 0 ≤ a) :
    Tendsto (fun n : ℕ ↦ (A a n : ℝ) / (n : ℝ)) atTop (nhds a) := by
  simpa only [A] using
    (tendsto_nat_floor_mul_div_atTop (R := ℝ) ha).comp
      tendsto_natCast_atTop_atTop

private theorem tendsto_C (c : ℝ) (hc : 0 ≤ c) :
    Tendsto (fun n : ℕ ↦ (C c n : ℝ) / (n : ℝ)) atTop (nhds c) := by
  simpa only [C] using
    (tendsto_nat_floor_mul_div_atTop (R := ℝ) hc).comp
      tendsto_natCast_atTop_atTop

private theorem tendsto_S (sigma : ℝ) (hsigma : 0 ≤ sigma) :
    Tendsto (fun n : ℕ ↦ (S sigma n : ℝ) / (n : ℝ))
      atTop (nhds sigma) := by
  simpa only [S] using
    (tendsto_nat_floor_mul_div_atTop (R := ℝ) hsigma).comp
      tendsto_natCast_atTop_atTop

private theorem tendsto_B
    (sigma c : ℝ) (hsigma : 0 ≤ sigma) (hc : 0 ≤ c)
    (hcs : c ≤ sigma) :
    Tendsto (fun n : ℕ ↦ (B sigma c n : ℝ) / (n : ℝ))
      atTop (nhds (sigma - c)) := by
  have hraw := (tendsto_S sigma hsigma).sub (tendsto_C c hc)
  apply hraw.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hCS := C_le_S sigma c hcs n
  rw [show B sigma c n = S sigma n - C c n by rfl,
    Nat.cast_sub hCS, sub_div]

private theorem tendsto_D
    (sigma a : ℝ) (hsigma : 0 ≤ sigma) (ha : 0 ≤ a)
    (hsa : sigma + a ≤ 1) :
    Tendsto (fun n : ℕ ↦ (D sigma a n : ℝ) / (n : ℝ))
      atTop (nhds (1 - sigma - a)) := by
  have hsum := (tendsto_S sigma hsigma).add (tendsto_A a ha)
  have hraw : Tendsto
      (fun n : ℕ ↦ (1 : ℝ) -
        ((S sigma n : ℝ) / (n : ℝ) +
          (A a n : ℝ) / (n : ℝ)))
      atTop (nhds (1 - (sigma + a))) :=
    tendsto_const_nhds.sub hsum
  have hD : Tendsto (fun n : ℕ ↦ (D sigma a n : ℝ) / (n : ℝ))
      atTop (nhds (1 - (sigma + a))) := hraw.congr' (by
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hSA := SA_le sigma a hsigma ha hsa n
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    rw [show D sigma a n = n - (S sigma n + A a n) by rfl,
      Nat.cast_sub hSA, Nat.cast_add, sub_div, div_self hn0]
    ring)
  have hlimit : 1 - (sigma + a) = 1 - sigma - a := by ring
  rw [hlimit] at hD
  exact hD

end MME.StothersFourth.Phi134Rounding

/-- Exact integer profiles approaching every feasible real symmetric
`phi_134` profile.  The construction remains valid when either omitted
weight `sigma-c` or `1-sigma-a` is zero. -/
theorem solution
    (sigma a c : ℝ) (ha : 0 < a) (hc : 0 < c)
    (hcs : c ≤ sigma) (hsa : sigma + a ≤ 1) :
    ∃ A B C D : ℕ → ℕ,
      (∀ n, A n + B n + C n + D n = n) ∧
      Tendsto (fun n : ℕ ↦ (A n : ℝ) / (n : ℝ)) atTop (nhds a) ∧
      Tendsto (fun n : ℕ ↦ (B n : ℝ) / (n : ℝ)) atTop
        (nhds (sigma - c)) ∧
      Tendsto (fun n : ℕ ↦ (C n : ℝ) / (n : ℝ)) atTop (nhds c) ∧
      Tendsto (fun n : ℕ ↦ (D n : ℝ) / (n : ℝ)) atTop
        (nhds (1 - sigma - a)) := by
  have hsigma : 0 ≤ sigma := (lt_of_lt_of_le hc hcs).le
  refine ⟨MME.StothersFourth.Phi134Rounding.A a,
    MME.StothersFourth.Phi134Rounding.B sigma c,
    MME.StothersFourth.Phi134Rounding.C c,
    MME.StothersFourth.Phi134Rounding.D sigma a, ?_⟩
  exact ⟨MME.StothersFourth.Phi134Rounding.exact_sum
      sigma a c hsigma ha.le hcs hsa,
    MME.StothersFourth.Phi134Rounding.tendsto_A a ha.le,
    MME.StothersFourth.Phi134Rounding.tendsto_B
      sigma c hsigma hc.le hcs,
    MME.StothersFourth.Phi134Rounding.tendsto_C c hc.le,
    MME.StothersFourth.Phi134Rounding.tendsto_D
      sigma a hsigma ha.le hsa⟩
