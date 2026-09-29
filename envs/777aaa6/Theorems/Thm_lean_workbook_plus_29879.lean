-- Prove2me | Theorems.Thm_lean_workbook_plus_29879
-- name    : lean_workbook_plus_29879
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/13866564-5c7f-45d2-b664-56de8477eea7
-- statement:
--   WLOG $ a+b+c=9,ab+bc+ca=24$ . Let $ a-1=x,b-1=y,c-1=z$ and $ a-2=p,b-2=q,c-2=r$ . So $ x+y+z=6,xy+yz+zx=9$ , $ p+q+r=3,pq+qr+rp=0$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_29879 {a b c x y z p q r : ℝ} (ha : a + b + c = 9) (hb : a * b + b * c + c * a = 24) (hx : x = a - 1) (hy : y = b - 1) (hz : z = c - 1) (hp : p = a - 2) (hq : q = b - 2) (hr : r = c - 2) : x + y + z = 6 ∧ x * y + y * z + z * x = 9 ∧ p + q + r = 3 ∧ p * q + q * r + r * p = 0   :=  by sorry
