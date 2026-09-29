-- Prove2me | Theorems.Thm_lean_workbook_plus_33417
-- name    : lean_workbook_plus_33417
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/04f7947a-69f0-4b3b-90c0-d0547b619f9a
-- statement:
--   $x \equiv y \bmod z$ is true if and only if $x - y$ is divisible by $z$ (or, actually, if you still want to think about it in terms of remainders, if $x$ and $y$ both give the same remainder upon division by $z$ ). For example, $15 \equiv 35 \bmod 20$ because $15 - 35 = -20$ , which is divisible by $20$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_33417 {x y z : ℤ} : x ≡ y [ZMOD z] ↔ z ∣ (x - y)   :=  by sorry
