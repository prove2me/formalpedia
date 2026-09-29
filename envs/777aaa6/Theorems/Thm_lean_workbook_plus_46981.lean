-- Prove2me | Theorems.Thm_lean_workbook_plus_46981
-- name    : lean_workbook_plus_46981
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/cbe80c0c-00ea-48ba-9051-2439a68829ec
-- statement:
--   On the basis of the Viete relations, we have: \(-\frac{b}{a}=\frac{p}{p-1}+\frac{p+1}{p}\), so \(b=-a\frac{2p^{2}-1}{p(p-1)}\), and \(\frac{c}{a}=\frac{p(p+1)}{p(p-1)}=\frac{p+1}{p-1}\) so \(c=a\frac{p+1}{p-1}\), thus \(a+b+c=a(1-\frac{2p^{2}-1}{p(p-1)}+\frac{p+1}{p-1})=a\frac{1}{p(p-1)}\) (1). Analogous \(b^{2}-4ac=a^{2}\left(\frac{2p^{2}-1}{p(p-1)}\right)^{2}-4a^{2}\frac{p+1}{p-1}=a^{2}\frac{1}{p^{2}(p-1)^{2}}\) (2)
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_46981  (a b c p : ℝ)
  (h₀ : 0 < p ∧ p ≠ 1)
  (h₁ : a ≠ 0)
  (h₂ : (p - 1) * (p + 1) = 1)
  (h₃ : b = -a * (2 * p^2 - 1) / (p * (p - 1)))
  (h₄ : c = a * (p + 1) / (p - 1)) :
  b^2 - 4 * a * c = a^2 / (p^2 * (p - 1)^2)   :=  by sorry
