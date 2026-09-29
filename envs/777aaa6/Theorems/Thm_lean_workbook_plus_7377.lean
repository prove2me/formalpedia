-- Prove2me | Theorems.Thm_lean_workbook_plus_7377
-- name    : lean_workbook_plus_7377
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/dd465534-208c-4c54-b305-5b368c753da8
-- statement:
--   $ \sum_{sym}f(a,b,c)=f(a,b,c)+f(a,c,b)+f(b,a,c)+f(b,c,a)+f(c,a,b)+f(c,b,a)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_7377 {α : Type} [AddCommMonoid α] (f : α → α → α → α) (a b c : α) :
  f a b c + f a c b + f b a c + f b c a + f c a b + f c b a = (fun x y z => f x y z + f x z y + f y x z + f y z x + f z x y + f z y x) a b c   :=  by sorry
