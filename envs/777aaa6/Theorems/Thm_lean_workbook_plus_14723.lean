-- Prove2me | Theorems.Thm_lean_workbook_plus_14723
-- name    : lean_workbook_plus_14723
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/16bb3181-8f91-4e8b-ab83-3757f572c2e9
-- statement:
--   2. $f^{-1}(Q)\cup f^{-1}(R)=f^{-1}(Q\cup R)$ \nIf $x\in f^{-1}(Q\cup R) \implies f(x)\in Q\cup R \implies f(x) \text{ is in } Q \text{ or } R \implies x\in f^{-1}(Q) \text{ or } f^{-1}(R) \implies x\in f^{-1}(Q)\cup f^{-1}(R)$ so $f^{-1}(Q\cup R)\subseteq f^{-1}(Q)\cup f^{-1}(R)$ . In a similar manner we can prove $f^{-1}(Q)\cup f^{-1}(R)\subseteq f^{-1}(Q\cup R)$ , so in fact $f^{-1}(Q)\cup f^{-1}(R)=f^{-1}(Q\cup R)$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14723 (f : X → Y) (Q R : Set Y) : f ⁻¹' Q ∪ f ⁻¹' R = f ⁻¹' (Q ∪ R)   :=  by sorry
