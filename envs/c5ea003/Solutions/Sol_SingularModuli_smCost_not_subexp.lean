-- Prove2me | solution 1 for SingularModuli.smCost_not_subexp
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-17T23:23:36.428293+00:00
-- url     : https://prove2.me/submissions/902aa3cc-ca53-4f48-83af-3055c77be413

import Mathlib
import Definitions.Def_Cryptography_FactoringBarriers_AsymptoticLadder
import Definitions.Def_Cryptography_SingularModuli_ExponentialRung

open SingularModuli

open Filter Real FactoringBarriers

open scoped Topology

namespace SingularModuli

private theorem subexp_const_mul {f : ℝ → ℝ} (hf : Subexp f) (c : ℝ) :
    Subexp (fun x => c * f x) := by
  intro ε hε
  have h := (hf ε hε).const_mul c
  rw [mul_zero] at h
  refine h.congr (fun x => ?_)
  rw [mul_div_assoc]

private theorem exp_linear_not_subexp {b : ℝ} (hb : 0 < b) :
    ¬ Subexp (fun x => Real.exp (b * x)) := by
  intro h
  have h2 := h (b / 2) (by linarith)
  have hgrow : Tendsto (fun x : ℝ => Real.exp (b * x) / Real.exp (b / 2 * x)) atTop atTop := by
    have : ∀ x : ℝ, Real.exp (b * x) / Real.exp (b / 2 * x) = Real.exp ((b / 2) * x) := by
      intro x; rw [← Real.exp_sub]; ring_nf
    simp only [this]
    exact Real.tendsto_exp_atTop.comp
      (Filter.Tendsto.const_mul_atTop (by linarith : (0:ℝ) < b / 2) tendsto_id)
  have := (hgrow.eventually (eventually_gt_atTop (1:ℝ))).and
    (h2.eventually (eventually_lt_nhds (by norm_num : (0:ℝ) < 1)))
  rcases this.exists with ⟨x, hx1, hx2⟩
  linarith

theorem solution {h : ℝ} (hh : 0 < h) : ¬ Subexp (smCost h) := by
  intro hsub
  have hmul := subexp_const_mul hsub (4 * h)
  have heq : (fun x => (4 * h) * smCost h x) = fun x => Real.exp (1 / 2 * x) := by
    funext x
    rw [smCost, mul_div_cancel₀ _ (by positivity : (4 : ℝ) * h ≠ 0),
      show (1:ℝ) / 2 * x = x / 2 by ring]
  rw [heq] at hmul
  exact exp_linear_not_subexp (by norm_num) hmul

end SingularModuli

open SingularModuli

theorem solution {h : ℝ} (hh : 0 < h) : ¬ Subexp (smCost h) :=
  SingularModuli.solution hh

#print axioms solution
