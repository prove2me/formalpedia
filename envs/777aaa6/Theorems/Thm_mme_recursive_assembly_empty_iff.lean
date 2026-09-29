-- Prove2me | Theorems.Thm_mme_recursive_assembly_empty_iff
-- name    : mme_recursive_assembly_empty_iff
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T07:06:25.313064+00:00
-- url     : https://prove2.me/theorems/32b2bbaa-b439-4d6e-98b2-f2ac25f27ecb
-- title:
--   Exact recursive assembly criterion with no factors and source power zero
-- statement:
--   Let $K$ be any field and let $D$ be recursive hash-extraction data with zero factors and source power zero. Write $r>0$ for its repair count and $a,b,c$ for its requested matrix dimensions. For any family $A$ of stages over these data,
--
--   $$\operatorname{RecursiveAssembly}(D,A,K)\iff r
--   e1\ \lor\ abc\le1.$$
--
--   This characterizes the degenerate assembly case: repair may discard the single empty-product copy, but retaining it requires a matrix tensor of volume at most one. Stage budgets alone do not impose that requirement.
-- source:
--   Exact analysis of the existing recursive assembly definition using the scalar-unit matrix restriction characterization.

import Definitions.Def_mme_recursive_yz_stage_certificate
open MME MME.HashExtraction MME.RecursiveYZ.Certificate
universe u
set_option autoImplicit false

theorem mme_recursive_assembly_empty_iff {K : Type u} [Field K]
    (D : Data) (A : ∀ j, Stage (D.hash j))
    (hfactors : D.factors = 0) (hpower : D.power = 0) :
    RecursiveAssembly D A K ↔ D.repairCopies ≠ 1 ∨ D.a * D.b * D.c ≤ 1 := by sorry
