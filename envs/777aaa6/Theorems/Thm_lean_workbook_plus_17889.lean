-- Prove2me | Theorems.Thm_lean_workbook_plus_17889
-- name    : lean_workbook_plus_17889
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/9bdee73a-f0a9-4f59-bba0-bc26b434c6e5
-- statement:
--   Let $ A\in\mathcal{M}_{n}(\mathbb{C})$ s.t. $ A$ commutates with $ AA^{*}-A^{*}A$ ; then $ AA^{*}-A^{*}A$ is a nilpotent matrix. Moreover $ AA^{*}-A^{*}A$ is a hermitian matrix and thus is diagonalizable. Conclusion: $ AA^{*}=A^{*}A$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_17889 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (h : A * A.conjTranspose - A.conjTranspose * A = 0) : A * A.conjTranspose = A.conjTranspose * A   :=  by sorry
