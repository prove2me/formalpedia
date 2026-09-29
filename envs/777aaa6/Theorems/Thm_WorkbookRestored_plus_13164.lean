-- Prove2me | Theorems.Thm_WorkbookRestored_plus_13164
-- name    : WorkbookRestored.plus_13164
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:13:59.582737+00:00
-- url     : https://prove2.me/theorems/3a7ebb56-9f4a-4d84-bff2-f535293c2119
-- title:
--   Classification of a twisted exponential functional equation
-- statement:
--   Fix $a>0$, $a\ne1$. A function $f:\mathbb R\to\mathbb R$ satisfies $f(x+y)=f(y)a^x$ for every $x,y$ if and only if $f(x)=ka^x$ for a real constant $k$.
--
--   This restores the missing imports or namespaces of [the original node](https://prove2.me/theorems/c6195dac-9c78-4073-ae3a-4937919f5f93), retaining its formal proposition. Source: Lean-Workbook row `lean_workbook_plus_13164` (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_13164; original Prove2Me node c6195dac-9c78-4073-ae3a-4937919f5f93; Apache-2.0

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
open Real

theorem WorkbookRestored.plus_13164 (a : ℝ) (ha : a ≠ 1) (ha' : a > 0) : ∀ f : ℝ → ℝ, (∀ x y : ℝ, f (x + y) = f y * a ^ x) ↔ ∃ k :ℝ, ∀ x : ℝ, f x = k * a ^ x   :=  by sorry
