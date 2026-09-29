-- Prove2me | Theorems.Thm_mme_entropy_regional_witness
-- name    : mme_entropy_regional_witness
-- status  : Disproved
-- author  : @WillR
-- created : 2026-09-15T07:23:18.808033+00:00
-- url     : https://prove2.me/theorems/cfe5ba9d-c93d-4b91-b3d9-b30ca6d19520
-- title:
--   Explicit entropy recipe with one input, five outputs and dimensions 25
-- statement:
--   Fix $N=2$ in the More Asymmetry regional setting. There is a finite entropy recipe $D$ at some level $ell$ with one charged input type, five guaranteed output copies, and matrix dimensions with product $25$. In particular $$inputs(D)=1, outputs(D)=5, a(D) b(D) c(D)=25.$$ This child isolates the combinatorial witness. The five dimensions come from a single $L=1$ boundary profile on the word $(1,1)$ ($5^2=25$); the five copies come from one descend level. No real-exponent surplus is claimed here.
--
--   **Formalization Note** Lean states the witness with fixed $N=2$ and existential level, predicate and recipe.
-- source:
--   Uniform entropy-based integer regional construction for the More Asymmetry matrix multiplication campaign, https://arxiv.org/html/2404.16349v2#S6 . This child isolates the combinatorial entropy-recipe witness; the real-exponent surplus is a separate child.

import Definitions.Def_mme_entropy_regional_CW_recipe
open MME MME.ProfiledCW MME.RegionRealization
set_option autoImplicit false

theorem mme_entropy_regional_witness : ∃ (ell : ℕ) (P : Predicate 2) (D : EntropyRecipe 2 ell P), D.inputs = 1 ∧ D.outputs = 5 ∧ D.a * D.b * D.c = 25 ∧ 1 ≤ D.a * D.b * D.c := by sorry
