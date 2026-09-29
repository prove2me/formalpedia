-- Prove2me | Theorems.Thm_lean_workbook_plus_75702
-- name    : lean_workbook_plus_75702
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/bf46b702-6dae-4b8c-ad77-089634ece00e
-- statement:
--   Prove that $ a$ is a quadratic residue $ \bmod p^n$ if and only if the polynomial $ x^2 - a \equiv 0 \bmod p^n$ has a solution. Also, prove that if $ f(a) \equiv 0 \bmod p$ then a solution $ \bmod p^2$ must reduce to a solution $ \bmod p$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_75702 {p : ℕ} (hp : p.Prime) {a : ℤ} {n : ℕ} : (∃ y, y^2 ≡ a [ZMOD p^n]) ↔ (∃ y, y^2 - a ≡ 0 [ZMOD p^n])   :=  by sorry
