-- Prove2me | solution 1 for ErdosProblems.Erdos243.PaperCompleteR11.reciprocal_cubic_scale_relations
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-24T23:43:21.859385+00:00
-- url     : https://prove2.me/submissions/25598f9c-2489-4c11-b089-721c8707dd1d

import Mathlib

namespace ErdosProblems.Erdos243.PaperCompleteR11
end ErdosProblems.Erdos243.PaperCompleteR11

                                                                    
                                                                           
                                         

namespace ErdosProblems.Erdos243.PaperCompleteR11
/-- Coefficient comparison for reciprocal cubic factors, without division. -/
theorem reciprocal_cubic_coefficient_factor
    {K : Type*} [Field K] (b d w : K)
    (h5 : b * w + d = 0)
    (h4 : d * w + b * d + b = -w) :
    (b * w - 1) * (b + w) = 0 := by
  linear_combination (b + w) * h5 - h4
end ErdosProblems.Erdos243.PaperCompleteR11

open ErdosProblems in
open ErdosProblems.Erdos243 in
open ErdosProblems.Erdos243.PaperCompleteR11 in
theorem solution
    {K : Type*} [Field K] (b d w η : K)
    (h5 : b * w + d = 0)
    (h4 : d * w + b * d + b = -w)
    (h3 : w ^ 2 + 1 + b ^ 2 + d ^ 2 = 8 * η * w) :
    (w ^ 2 + 1) ^ 2 = 8 * η * w ^ 3 ∨
      (w ^ 2 + 1) ^ 2 = 8 * η * w := by
  have hfactor := reciprocal_cubic_coefficient_factor b d w h5 h4
  rcases mul_eq_zero.mp hfactor with hb | hb
  · left
    have hd : d = -1 := by linear_combination h5 - hb
    rw [hd] at h3
    linear_combination w ^ 2 * h3 - (b * w + 1) * hb
  · right
    have hb' : b = -w := by linear_combination hb
    rw [hb'] at h5 h3
    have hd : d = w ^ 2 := by linear_combination h5
    rw [hd] at h3
    linear_combination h3
