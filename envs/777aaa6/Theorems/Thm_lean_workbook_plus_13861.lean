-- Prove2me | Theorems.Thm_lean_workbook_plus_13861
-- name    : lean_workbook_plus_13861
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/385be683-ea4e-4b05-890f-2ee3c9adced4
-- statement:
--   If $a \equiv b \pmod{m}$ and $p \equiv q \pmod{m}$ : \n\n1. $a+c \equiv b+c \pmod{m}$ \n2. $ac \equiv bc \pmod{m}$ \n3. $a^{c} \equiv b^{c} \pmod{m}$ \n4. $(a+p) \equiv (b+q) \pmod{m}$ \n5. $ap \equiv bq \pmod{m}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_13861 {a b c m : ℤ} (h₁ : a ≡ b [ZMOD m]) : a + c ≡ b + c [ZMOD m]   :=  by sorry
