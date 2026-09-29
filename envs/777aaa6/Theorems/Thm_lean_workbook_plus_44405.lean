-- Prove2me | Theorems.Thm_lean_workbook_plus_44405
-- name    : lean_workbook_plus_44405
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/c6252be7-cc7e-497e-9353-4fc26b792120
-- statement:
--   For integers $a,x,y$ and prime number $p$ , where $p$ doesn't divide $a$ , prove that if $xa \equiv ya \pmod p$ and $0 < x,y \leq p$, then $x=y$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_44405 (a x y p : ℤ) (hp : Prime p) (hpa : ¬ p ∣ a) (h0 : 0 < x ∧ 0 < y) (hxp : x ≤ p) (hyp : y ≤ p) (h : x * a ≡ y * a [ZMOD p]) : x ≡ y [ZMOD p]   :=  by sorry
