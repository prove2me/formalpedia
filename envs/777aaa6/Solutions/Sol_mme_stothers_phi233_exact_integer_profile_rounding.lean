-- Prove2me | solution 1 for mme_stothers_phi233_exact_integer_profile_rounding
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T21:27:16.362513+00:00
-- url     : https://prove2.me/submissions/351bb75c-249c-4c3b-9f8a-aa58a330929f

import Mathlib.Analysis.SpecificLimits.Basic

open Filter

set_option autoImplicit false
set_option warningAsError true

namespace MME.StothersFourth.Phi233Rounding

private noncomputable def A (a : ℝ) (n : ℕ) : ℕ :=
  ⌊a * (n : ℝ)⌋₊

private noncomputable def B (b : ℝ) (n : ℕ) : ℕ :=
  ⌊b * (n : ℝ)⌋₊

private noncomputable def C (c : ℝ) (n : ℕ) : ℕ :=
  ⌊c * (n : ℝ)⌋₊

private noncomputable def D (a b c : ℝ) (n : ℕ) : ℕ :=
  n - (2 * A a n + B b n + C c n)

private theorem partial_sum_le
    (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hsum : 2 * a + b + c + d = 1) (hd : 0 ≤ d) (n : ℕ) :
    2 * A a n + B b n + C c n ≤ n := by
  have hA : ((A a n : ℕ) : ℝ) ≤ a * (n : ℝ) := by
    exact Nat.floor_le (mul_nonneg ha (by positivity))
  have hB : ((B b n : ℕ) : ℝ) ≤ b * (n : ℝ) := by
    exact Nat.floor_le (mul_nonneg hb (by positivity))
  have hC : ((C c n : ℕ) : ℝ) ≤ c * (n : ℝ) := by
    exact Nat.floor_le (mul_nonneg hc (by positivity))
  have hcoef : 2 * a + b + c ≤ 1 := by linarith
  have hn : 0 ≤ (n : ℝ) := by positivity
  have hreal :
      (((2 * A a n + B b n + C c n : ℕ) : ℝ)) ≤ (n : ℝ) := by
    push_cast
    calc
      2 * (A a n : ℝ) + (B b n : ℝ) + (C c n : ℝ) ≤
          2 * (a * (n : ℝ)) + b * (n : ℝ) + c * (n : ℝ) := by
        gcongr
      _ = (2 * a + b + c) * (n : ℝ) := by ring
      _ ≤ 1 * (n : ℝ) := mul_le_mul_of_nonneg_right hcoef hn
      _ = (n : ℝ) := one_mul _
  exact_mod_cast hreal

private theorem exact_sum
    (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hd : 0 ≤ d) (hsum : 2 * a + b + c + d = 1) (n : ℕ) :
    2 * A a n + B b n + C c n + D a b c n = n := by
  unfold D
  exact Nat.add_sub_of_le (partial_sum_le a b c d ha hb hc hsum hd n)

private theorem tendsto_A (a : ℝ) (ha : 0 ≤ a) :
    Tendsto (fun n : ℕ ↦ (A a n : ℝ) / (n : ℝ)) atTop (nhds a) := by
  simpa only [A] using
    (tendsto_nat_floor_mul_div_atTop (R := ℝ) ha).comp
      tendsto_natCast_atTop_atTop

private theorem tendsto_B (b : ℝ) (hb : 0 ≤ b) :
    Tendsto (fun n : ℕ ↦ (B b n : ℝ) / (n : ℝ)) atTop (nhds b) := by
  simpa only [B] using
    (tendsto_nat_floor_mul_div_atTop (R := ℝ) hb).comp
      tendsto_natCast_atTop_atTop

private theorem tendsto_C (c : ℝ) (hc : 0 ≤ c) :
    Tendsto (fun n : ℕ ↦ (C c n : ℝ) / (n : ℝ)) atTop (nhds c) := by
  simpa only [C] using
    (tendsto_nat_floor_mul_div_atTop (R := ℝ) hc).comp
      tendsto_natCast_atTop_atTop

private theorem tendsto_D
    (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hd : 0 ≤ d) (hsum : 2 * a + b + c + d = 1) :
    Tendsto (fun n : ℕ ↦ (D a b c n : ℝ) / (n : ℝ)) atTop (nhds d) := by
  have hABC : Tendsto
      (fun n : ℕ ↦
        2 * ((A a n : ℝ) / (n : ℝ)) +
          (B b n : ℝ) / (n : ℝ) + (C c n : ℝ) / (n : ℝ))
      atTop (nhds (2 * a + b + c)) :=
    (((tendsto_A a ha).const_mul 2).add (tendsto_B b hb)).add
      (tendsto_C c hc)
  have hraw : Tendsto
      (fun n : ℕ ↦
        (1 : ℝ) -
          (2 * ((A a n : ℝ) / (n : ℝ)) +
            (B b n : ℝ) / (n : ℝ) + (C c n : ℝ) / (n : ℝ)))
      atTop (nhds (1 - (2 * a + b + c))) :=
    tendsto_const_nhds.sub hABC
  have hD : Tendsto
      (fun n : ℕ ↦ (D a b c n : ℝ) / (n : ℝ))
      atTop (nhds (1 - (2 * a + b + c))) := hraw.congr' (by
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hle := partial_sum_le a b c d ha hb hc hsum hd n
    have hnReal : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    rw [show D a b c n = n - (2 * A a n + B b n + C c n) by rfl,
      Nat.cast_sub hle, Nat.cast_add, Nat.cast_add, Nat.cast_mul,
      Nat.cast_ofNat, sub_div, div_self hnReal]
    ring)
  have hlimit : 1 - (2 * a + b + c) = d := by linarith
  rw [hlimit] at hD
  exact hD

end MME.StothersFourth.Phi233Rounding

/-- Exact integer profiles approaching any feasible real `phi_233` profile. -/
theorem solution
    (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hsum : 2 * a + b + c + d = 1) :
    ∃ A B C D : ℕ → ℕ,
      (∀ n, 2 * A n + B n + C n + D n = n) ∧
      Tendsto (fun n : ℕ ↦ (A n : ℝ) / (n : ℝ)) atTop (nhds a) ∧
      Tendsto (fun n : ℕ ↦ (B n : ℝ) / (n : ℝ)) atTop (nhds b) ∧
      Tendsto (fun n : ℕ ↦ (C n : ℝ) / (n : ℝ)) atTop (nhds c) ∧
      Tendsto (fun n : ℕ ↦ (D n : ℝ) / (n : ℝ)) atTop (nhds d) := by
  refine ⟨MME.StothersFourth.Phi233Rounding.A a,
    MME.StothersFourth.Phi233Rounding.B b,
    MME.StothersFourth.Phi233Rounding.C c,
    MME.StothersFourth.Phi233Rounding.D a b c, ?_⟩
  exact ⟨MME.StothersFourth.Phi233Rounding.exact_sum
      a b c d ha hb hc hd hsum,
    MME.StothersFourth.Phi233Rounding.tendsto_A a ha,
    MME.StothersFourth.Phi233Rounding.tendsto_B b hb,
    MME.StothersFourth.Phi233Rounding.tendsto_C c hc,
    MME.StothersFourth.Phi233Rounding.tendsto_D
      a b c d ha hb hc hd hsum⟩
