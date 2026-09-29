-- Prove2me | Theorems.Thm_lean_workbook_plus_76410
-- name    : lean_workbook_plus_76410
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/986a8bd5-2afa-4fc8-abe6-61b9a3ad60e5
-- statement:
--   Prove the property $n \equiv b \pmod{c} \Rightarrow n^a \equiv b^a \pmod{c}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_76410 : ∀ {n b c a : ℕ}, n ≡ b [ZMOD c] → n ^ a ≡ b ^ a [ZMOD c]   :=  by sorry
