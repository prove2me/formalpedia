-- Prove2me | Theorems.Thm_lean_workbook_plus_60316
-- name    : lean_workbook_plus_60316
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/14d9960e-2b6d-4eb9-9d74-94eeaae1561b
-- statement:
--   Let $p$ be the probability that $\lceil\log_4x\rceil$ is odd when $x$ is randomly chosen from the interval $(0,1]$ . We can see that this is the same as the probability that $\lceil\log_4(4x)\rceil$ is odd when $x$ is randomly chosen from the interval $\left(0,\frac14\right]$ . Furthermore, $\lceil\log_4(4x)\rceil=\lceil\log_4x+1\rceil=\lceil\log_4x\rceil+1$ , which shows that $\lceil\log_4(4x)\rceil$ is odd if and only if $x$ is even. Hence, the probability that $\lceil\log_4x\rceil$ is odd when $x$ is randomly chosen from the interval $\left(0,\frac14\right]$ is equal to $1-p$ . Therefore, the probability that $\lceil\log_4x\rceil$ is odd when $x$ is randomly chosen from the interval $(0,1]$ can also be expressed as: $p=\frac14(1-p)$ Solving for $p$ gives us $p=\frac15$ . Therefore, the probability that $y$ is odd when $x$ is randomly chosen from $(0,1]$ is $\boxed{\frac15}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_60316  (p : ℝ)
  (h₀ : p = 1 / 4 * (1 - p)) :
  p = 1 / 5   :=  by sorry
