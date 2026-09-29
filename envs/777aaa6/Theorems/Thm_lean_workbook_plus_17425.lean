-- Prove2me | Theorems.Thm_lean_workbook_plus_17425
-- name    : lean_workbook_plus_17425
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/ae09e911-1be0-41c0-bec9-5c111190a78f
-- statement:
--   During a period of days, we observed that when it rained in the afternoon, it had been clear in the morning, and when it rained in the morning, it was clear in the afternoon. It rained on 9 days, and it was clear on 6 afternoons and 7 mornings. How long was this period?\n\nA. 16 days\nb.14 days\nc.13 days\nd.12 days\ne. 11 days\nNote that in the given context, it is impossible for it to rain both in the morning and the afternoon. The possible situations are that it rained in the morning and was clear in the afternoon, it was clear in the morning and rained in the afternoon, or it was clear in the morning and the afternoon. Let $m$ be the number of days it rained in the morning (and was clear in the afternoon), $a$ be the number of days it rained in the afternoon (and was clear in the morning), and $n$ be the number of days it did not rain at all. We seek $m + a + n$ because there is no overlap between these events. We obtain the system of equations:\n\n $m + a = 9$\n $m + n = 7$\n $a + n = 6$\n\nWe could solve, but we don't need to know $a, m, n$ . We only want $m + a + n$ . Adding the three equations gives $2m + 2a + 2n = 22$ , so $m + a + n = 11 \implies \boxed{E}$\n\nWe know that it rained on $9$ days, and that $a$ is the number of days it rained in the afternoon and $m$ is the number of days it rained in the morning. Therefore, $m+a = 9.$\n\nSimilarly, $m$ is the number of days it was clear in the afternoon (and rainy in the morning) and $n$ is the number of days it was clear at both times. So, $m+n=7.$\n\nLastly, $a$ is the number of days it was clear in the morning (and rainy in the afternoon), and $n$ is the number of days it was clear at both times. So, $a+n = 6.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_17425  (m a n : ℕ)
  (h₀ : m + a = 9)
  (h₁ : m + n = 7)
  (h₂ : a + n = 6) :
  m + a + n = 11   :=  by sorry
