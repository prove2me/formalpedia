-- Prove2me | Theorems.Thm_WorkbookSyntax_plus_45249
-- name    : WorkbookSyntax.plus_45249
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:06:40.536982+00:00
-- url     : https://prove2.me/theorems/2157d9a3-eb4a-4426-a06e-14e717e71540
-- title:
--   Lean-Workbook Syntax 45249: Counting integers coprime to n
-- statement:
--   For every natural $n>1$, the number of integers $k$ with $1\le k\le n$ and $\gcd(k,n)=1$ equals $\varphi(n)$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_45249` (Apache-2.0), [original record](https://prove2.me/theorems/1e10d4c4-addf-4a3d-b30e-5ee36a2843d3). This corrected declaration replaces the obsolete finite sum/product binder `in` with `∈` and restores required imports or namespaces. Ranges, casts, quantifiers, and mathematical expressions are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_45249; immutable original Prove2Me node 1e10d4c4-addf-4a3d-b30e-5ee36a2843d3

import Mathlib.Data.Nat.Totient

theorem WorkbookSyntax.plus_45249 : ∀ n : ℕ, 1 < n → ∑ k ∈ Finset.filter (fun k => Nat.gcd k n = 1) (Finset.Icc 1 n), 1 = Nat.totient n   :=  by sorry
