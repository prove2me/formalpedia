-- Prove2me | Theorems.Thm_lean_workbook_plus_59071
-- name    : lean_workbook_plus_59071
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/dc9f807d-6ce1-4d90-91b5-383d5114933c
-- statement:
--   Evaluate \(\dfrac{3 \times 5 \times 7}{2 \times 4} + \dfrac{5 \times 7 \times 9}{4 \times 6} + ... + \dfrac{17 \times 19 \times 21}{16 \times 18}\)Summation OverkillEach term can be expressed as: \(\frac{(2n+1)(2n+3)(2n+5)}{2n(2n+2)}=\frac{8n^3+36n^2+46n+15}{4n^2+4n}=2n+7+\left(\frac{3}{4}\right)\left(\frac{6n+5}{n^2+n}\right)\)for \(n=1,2\cdots{8}\) . Writing as a summation, we have \(\sum_{n=1}^{8}\left(\frac{(2n+1)(2n+3)(2n+5)}{2n(2n+2)}\right)=\sum_{n=1}^{8}\left(2n+7+\left(\frac{3}{4}\right)\left(\frac{6n+5}{n^2+n}\right)\right)=2\left(\sum_{n=1}^{8}n\right)+7+\left(\frac{3}{4}\right)\left(\sum_{n=1}^{8}\left(\frac{6n+5}{n^2+n}\right)\right)\)The first summation is pretty easy. For the second one, yes, we need to bash, because the sum does not converge. After bashing, we get the sum as \(\frac{19427}{1260}\) . Continuing to simplify we finally get: \(2\left(\sum_{n=1}^{8}n\right)+7+\left(\frac{3}{4}\right)\left(\sum_{n=1}^{8}\left(\frac{6n+5}{n^2+n}\right)\right)=79+\left(\frac{3}{4}\right)\left(\frac{19427}{1260}\right)=79+\frac{19427}{1680}=\boxed{\frac{152147}{1680}}\) .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_59071 :
  ∑ k in Finset.Icc 1 8, ((2 * k + 1) * (2 * k + 3) * (2 * k + 5)) / (2 * k * (2 * k + 2)) = 152147 / 1680   :=  by sorry
