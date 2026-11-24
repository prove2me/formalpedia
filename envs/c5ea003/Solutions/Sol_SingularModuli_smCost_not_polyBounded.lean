-- Prove2me | solution 1 for SingularModuli.smCost_not_polyBounded
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-17T23:23:37.269439+00:00
-- url     : https://prove2.me/submissions/4903f60f-d596-4a08-b50b-c0d949a8e78f

import Mathlib
import Definitions.Def_Cryptography_FactoringBarriers_AsymptoticLadder
import Definitions.Def_Cryptography_SingularModuli_ExponentialRung

open SingularModuli

open Filter Real FactoringBarriers

open scoped Topology

namespace SingularModuli

private theorem superpoly_div_const {f : ℝ → ℝ} (hf : Superpoly f) {c : ℝ} (hc : 0 < c) :
    Superpoly (fun x => f x / c) := by
  intro d
  have h := (hf d).atTop_div_const hc
  refine h.congr (fun x => ?_)
  rw [div_div, div_div, mul_comm]

private theorem superpoly_smCost {h : ℝ} (hh : 0 < h) : Superpoly (smCost h) := by
  have hbase : Superpoly (fun x : ℝ => Real.exp (1 / 2 * x)) :=
    Superpoly_exp_linear (by norm_num)
  have hdiv := superpoly_div_const hbase (by positivity : (0:ℝ) < 4 * h)
  have heq : (fun x : ℝ => Real.exp (1 / 2 * x) / (4 * h)) = smCost h := by
    funext x
    rw [smCost, show (1:ℝ) / 2 * x = x / 2 by ring]
  rwa [heq] at hdiv

private theorem not_polyBounded_of_superpoly {f : ℝ → ℝ} (hf : Superpoly f) :
    ¬ PolyBounded f := by
  rintro ⟨C, d, hCd⟩
  have hdiv : Tendsto (fun x => f x / x ^ d) atTop atTop := hf d
  have hbdd : ∀ᶠ x : ℝ in atTop, f x / x ^ d ≤ C := by
    filter_upwards [hCd, eventually_gt_atTop (0 : ℝ)] with x hx hx0
    rw [div_le_iff₀ (Real.rpow_pos_of_pos hx0 d)]
    linarith [hx]
  have := (hdiv.eventually (eventually_gt_atTop C)).and hbdd
  rcases this.exists with ⟨x, h1, h2⟩
  linarith

theorem solution {h : ℝ} (hh : 0 < h) : ¬ PolyBounded (smCost h) :=
  not_polyBounded_of_superpoly (superpoly_smCost hh)

end SingularModuli

open SingularModuli

theorem solution {h : ℝ} (hh : 0 < h) : ¬ PolyBounded (smCost h) :=
  SingularModuli.solution hh

#print axioms solution
