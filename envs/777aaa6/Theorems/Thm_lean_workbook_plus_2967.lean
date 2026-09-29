-- Prove2me | Theorems.Thm_lean_workbook_plus_2967
-- name    : lean_workbook_plus_2967
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/c85773fb-efeb-48c2-bbbd-b4cac44e5003
-- statement:
--   Let the initial population of Sudbury be $s$ and the initial population of Victoria be $v$ . All we want is $ \frac {s}{v} $ .\nNow, poplulation of sudsbury decreased be $6%$ , so at the end of 1996, the population became $ s-(\frac {6}{100} \times s)= s\times(\frac{94}{100})$ .\nSimilarly, the new population of Victoria will be $v+(\frac{14}{100}\times v)= v\times (\frac{114}{100})$ .\nAccording to the condition, $v\times (\frac{114}{100}) = s\times(\frac{94}{100})$ .\n\nWhy does s/v=57/47?\n\nWe know $v\times (\frac{114}{100}) = s\times(\frac{94}{100}) $ .\nThen when we simplify, we get, $ \frac{s}{v}=\frac{114\times100}{94\times100}=\frac{57}{47}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_2967  (s v : ℝ)
  (h₀ : 0 < s ∧ 0 < v)
  (h₁ : v * (114 / 100) = s * (94 / 100)) :
  s / v = 57 / 47   :=  by sorry
