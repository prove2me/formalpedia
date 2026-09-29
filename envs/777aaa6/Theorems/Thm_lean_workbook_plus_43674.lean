-- Prove2me | Theorems.Thm_lean_workbook_plus_43674
-- name    : lean_workbook_plus_43674
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/c35e2d30-cbd5-4aad-b6db-5603503a3a9a
-- statement:
--   i) We have $a+bi\equiv c+di\mod (2)$ if and only if $(a+bi)-(c+di)\in (2)$ , if and only if there exist $p,q\in \mathbb{Z}$ such that $(a+bi)-(c+di)=2(p+qi)$ , if and only if there exist $p,q\in \mathbb{Z}$ such that $a-c=2p$ and $b-d=2q$ , if and only if $a\equiv c\pmod 2$ and $b\equiv d\pmod 2$ . Hence the elments are the equivalence classes of $0$ , $1$ , $i$ and $1+i$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_43674 : ∀ a b c d : ℤ, a + b * ℑ ≡ c + d * ℑ [ZMOD 2] ↔ a ≡ c [ZMOD 2] ∧ b ≡ d [ZMOD 2]   :=  by sorry
