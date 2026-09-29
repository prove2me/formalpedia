-- Prove2me | solution 1 for mme_vanishing_error_dominates_linear_sqrt_loss
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T08:07:19.924102+00:00
-- url     : https://prove2.me/submissions/32ce8bf1-265c-4a08-b102-c5d733513ae4

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

open Filter Topology

set_option autoImplicit false
set_option warningAsError true

theorem solution
    (error : ℕ → ℝ) (herror : Tendsto error atTop (nhds 0))
    (count scale : ℕ) (hcount : 0 < count) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ m : ℕ in atTop,
        Real.exp
            (-C * Real.sqrt (((scale * m + 1 : ℕ) : ℝ))) ≤
          1 - error (count * m) := by
  refine ⟨1, by norm_num, ?_⟩
  let epsilon : ℝ := 1 - Real.exp (-1)
  have hepsilon : 0 < epsilon := by
    dsimp [epsilon]
    exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (by norm_num))
  have hsmall : ∀ᶠ n : ℕ in atTop, error n < epsilon :=
    (tendsto_order.1 herror).2 epsilon hepsilon
  have hlinear : Tendsto (fun m : ℕ ↦ count * m) atTop atTop := by
    simpa [nsmul_eq_mul, mul_comm] using
      ((tendsto_id : Tendsto (fun x : ℕ ↦ x) atTop atTop).nsmul_atTop
        hcount)
  have hpulled := hlinear.eventually hsmall
  filter_upwards [hpulled] with m hm
  have hone_le :
      (1 : ℝ) ≤ (((scale * m + 1 : ℕ) : ℝ)) := by
    push_cast
    exact le_add_of_nonneg_left
      (mul_nonneg (Nat.cast_nonneg scale) (Nat.cast_nonneg m))
  have hsqrt :
      (1 : ℝ) ≤ Real.sqrt (((scale * m + 1 : ℕ) : ℝ)) := by
    have h := Real.sqrt_le_sqrt hone_le
    norm_num at h ⊢
    exact h
  have hexp :
      Real.exp
          (-(1 : ℝ) * Real.sqrt (((scale * m + 1 : ℕ) : ℝ))) ≤
        Real.exp (-1) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  calc
    Real.exp
          (-(1 : ℝ) * Real.sqrt (((scale * m + 1 : ℕ) : ℝ))) ≤
        Real.exp (-1) := hexp
    _ ≤ 1 - error (count * m) := by
      dsimp [epsilon] at hm
      linarith
