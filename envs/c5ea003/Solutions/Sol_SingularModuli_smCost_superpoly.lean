-- Prove2me | solution 1 for SingularModuli.smCost_superpoly
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-17T23:16:57.60785+00:00
-- url     : https://prove2.me/submissions/36358c78-0886-485f-b6ea-56d40b93f995

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

theorem solution {h : ℝ} (hh : 0 < h) : Superpoly (smCost h) := by
  have hbase : Superpoly (fun x : ℝ => Real.exp (1 / 2 * x)) :=
    Superpoly_exp_linear (by norm_num)
  have hdiv := superpoly_div_const hbase (by positivity : (0:ℝ) < 4 * h)
  have heq : (fun x : ℝ => Real.exp (1 / 2 * x) / (4 * h)) = smCost h := by
    funext x
    rw [smCost, show (1:ℝ) / 2 * x = x / 2 by ring]
  rwa [heq] at hdiv

end SingularModuli

open SingularModuli

theorem solution {h : ℝ} (hh : 0 < h) : Superpoly (smCost h) :=
  SingularModuli.solution hh

#print axioms solution
