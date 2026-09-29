-- Prove2me | Theorems.Thm_WorkbookSyntax_plus_49771
-- name    : WorkbookSyntax.plus_49771
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:06:38.962313+00:00
-- url     : https://prove2.me/theorems/7feda76e-8672-45eb-b39d-7ce8e9847f8a
-- title:
--   Lean-Workbook Syntax 49771: A finite binomial convolution identity
-- statement:
--   $\sum_{m=0}^{15}\sum_{n=0}^{15-m}\binom{m+n}{m}\binom{15}{m+n}5^n=\sum_{m=0}^{15}\binom{15}{m}6^{15-m}$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_49771` (Apache-2.0), [original record](https://prove2.me/theorems/7c709cbb-5fcf-49fe-b6f6-8a68e9b4b68c). This corrected declaration replaces the obsolete finite sum/product binder `in` with `∈` and restores required imports or namespaces. Ranges, casts, quantifiers, and mathematical expressions are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_49771; immutable original Prove2Me node 7c709cbb-5fcf-49fe-b6f6-8a68e9b4b68c

import Mathlib.Data.Nat.Choose.Sum

theorem WorkbookSyntax.plus_49771 : ∑ m ∈ Finset.range 16, ∑ n ∈ Finset.range (16 - m), (Nat.choose (m + n) m * Nat.choose 15 (m + n) * 5 ^ n) = ∑ m ∈ Finset.range 16, (Nat.choose 15 m * 6 ^ (15 - m))   :=  by sorry
