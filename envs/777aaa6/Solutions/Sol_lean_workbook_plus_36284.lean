-- Prove2me | solution 1 for lean_workbook_plus_36284
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T22:48:02.80154+00:00
-- url     : https://prove2.me/submissions/3ebe75b8-2812-44aa-bbed-42d7eedca8c3

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution : (√ 2) / (√ (2 + √ 2) * √ (2 + √ (2 + √ 2))) = √ (2 - √ (2 + √ 2)) := by
  let r : ℝ := Real.sqrt 2
  let s : ℝ := Real.sqrt (2+r)
  let t : ℝ := Real.sqrt (2+s)
  let u : ℝ := Real.sqrt (2-s)
  have hr : r^2=2 := Real.sq_sqrt (by norm_num)
  have hrp : 0 < r := Real.sqrt_pos.2 (by norm_num)
  have hr2 : r≤2 := by nlinarith only [hr,hrp]
  have hs : s^2=2+r := Real.sq_sqrt (by positivity)
  have hsp : 0 < s := Real.sqrt_pos.2 (by positivity)
  have hs2 : s≤2 := by nlinarith only [hs,hsp,hr2]
  have ht : t^2=2+s := Real.sq_sqrt (by positivity)
  have htp : 0 < t := Real.sqrt_pos.2 (by positivity)
  have hu : u^2=2-s := Real.sq_sqrt (by linarith)
  have hun : 0≤u := Real.sqrt_nonneg _
  have htu : (t*u)^2=2-r := by
    calc
      (t*u)^2=t^2*u^2 := by ring
      _=(2+s)*(2-s) := by rw [ht,hu]
      _=2-r := by nlinarith only [hs]
  have hprod : (s*(t*u))^2=2 := by
    calc
      (s*(t*u))^2=s^2*(t*u)^2 := by ring
      _=(2+r)*(2-r) := by rw [hs,htu]
      _=2 := by nlinarith only [hr]
  have hpn : 0≤s*(t*u) := by positivity
  have he : s*(t*u)=r := by nlinarith only [hprod,hr,hpn,hrp]
  change r/(s*t)=u
  apply (div_eq_iff (ne_of_gt (mul_pos hsp htp))).2
  nlinarith only [he]
