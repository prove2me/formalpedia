-- Prove2me | Theorems.Thm_lean_workbook_plus_30115
-- name    : lean_workbook_plus_30115
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/836fa800-7680-43cf-b6e5-877e165e49cb
-- statement:
--   With decipherable LaTeX\n$p$ is a prime number such that $p \equiv 7$ $(\mod 8)$ then prove that $2$ is a quadratic residue $\mod$ $p$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_30115 {p : ℕ} (hp : p.Prime) (hpo : p ≡ 7 [ZMOD 8]) : ((2 : ZMod p) ^ 2 = 4)   :=  by sorry
