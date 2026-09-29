-- Prove2me | Theorems.Thm_lean_workbook_plus_81180
-- name    : lean_workbook_plus_81180
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/95844202-05e3-4fc8-8586-cc1e94f1cb4f
-- statement:
--   Let $G$ be an abelian group of order $n$. If $f:G\to \mathbb{C}$ is a function, then prove that for all $h\in G$, $\sum_{g\in G}f(g)=\sum_{g\in G}f(hg)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_81180 (G : Type*) [Fintype G] [CommGroup G] (f : G → ℂ) (h : G) : ∑ g : G, f g = ∑ g : G, f (h * g)   :=  by sorry
