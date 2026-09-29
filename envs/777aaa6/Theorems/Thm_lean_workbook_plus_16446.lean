-- Prove2me | Theorems.Thm_lean_workbook_plus_16446
-- name    : lean_workbook_plus_16446
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/5e007bb9-95a5-4ad1-aed4-e5736cc21594
-- statement:
--   We wish to calculate $$1998^{1999} + 1999^{1998} \pmod{7}.$$ We first note that $(1998,7) = (1999,7) = 1$ . By Fermat's Little Theorem, we have that $a^6 \equiv 1 \pmod{7}$ . \n\nWe have that $1998 = 6 \cdot 333$ from which we have that $1999^{1998} \equiv 1 \pmod{7}$ and since $1999 = 6 \cdot 333 +1$ that $1998^{1999} \equiv 1998 \pmod{7} \equiv 3 \pmod{7}$ \n\nThus we have $1998^{1999} + 1999^{1998} \equiv 1 +3 \pmod{7} \equiv 4 \pmod{7}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_16446 :
  (1998^1999 + 1999^1998) % 7 = 4   :=  by sorry
