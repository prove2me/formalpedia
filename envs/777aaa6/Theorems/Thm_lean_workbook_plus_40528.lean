-- Prove2me | Theorems.Thm_lean_workbook_plus_40528
-- name    : lean_workbook_plus_40528
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/65fd61cc-6c55-4997-b859-a06aa411c3ca
-- statement:
--   prove that if $a|x$ and $a|y$ , then: \n $a|x+y$ \n $a|x-y$ \n $a|px+qy$ for $p$ , $q$ integers
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_40528 : ∀ {a x y : ℤ} (h₁ : a ∣ x) (h₂ : a ∣ y), a ∣ x + y ∧ a ∣ x - y ∧ ∀ p q : ℤ, a ∣ p * x + q * y   :=  by sorry
