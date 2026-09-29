-- Prove2me | Theorems.Thm_lean_workbook_plus_9644
-- name    : lean_workbook_plus_9644
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/c83aaa96-0760-4139-9ce6-e72c03ff9564
-- statement:
--   Substitute $x=t-\frac{\pi}{15}$ : \n $2 \sin(\frac{\pi }{3}-\frac{t}{2})-\sin(\frac{3t}{2})=0$ \n $2 \sin \frac{\pi }{3}\cos \frac{t}{2} - 2 \sin \frac{t}{2}\cos \frac{\pi }{3}- 3\sin \frac{t}{2}+4 \sin^{3}\frac{t}{2}=0$ \n $\sqrt{3}\cos \frac{t}{2}- \sin \frac{t}{2}- 3\sin \frac{t}{2}+4 \sin^{3}\frac{t}{2}=0$ \n $\sqrt{3}\cos \frac{t}{2}- 4\sin \frac{t}{2}+4 \sin^{3}\frac{t}{2}=0$ \n $\sqrt{3}\cos \frac{t}{2}- 4\sin \frac{t}{2}(1- \sin^{2}\frac{t}{2})=0$ \n $\sqrt{3}\cos \frac{t}{2}- 4\sin \frac{t}{2} \cos^{2}\frac{t}{2}=0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_9644 :
  ∀ t : ℝ, (Real.sqrt 3 * Real.cos (t / 2) - 4 * Real.sin (t / 2) * (Real.cos (t / 2))^2 = 0)   :=  by sorry
