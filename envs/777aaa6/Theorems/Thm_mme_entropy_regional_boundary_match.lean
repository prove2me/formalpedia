-- Prove2me | Theorems.Thm_mme_entropy_regional_boundary_match
-- name    : mme_entropy_regional_boundary_match
-- status  : Disproved
-- author  : @WillR
-- created : 2026-09-15T12:05:33.026468+00:00
-- url     : https://prove2.me/theorems/cc7074e1-cc69-4cce-bd3d-a56320d99474
-- title:
--   Boundary data with dimensions 25 matching a given step output
-- statement:
--   Fix $N=2$ and any level $lower$. For every integer entropy step $S$ over the trivial predicate there is finite boundary data $B$ at the same level, over the step's own output predicate $S.output$, whose matrix dimensions multiply to $25$. In particular $$a(B)b(B)c(B)=25.$$ This child isolates the combinatorial boundary half of the witness: a single level-two profile on the word $(1,1)$ contributes $5^2=25$, and the boundary construction must align its grade and usefulness conditions with the given step output. It takes the step as a hypothesis so the two halves share one level and one output predicate.
--
--   **Formalization Note** Lean quantifies over the level and the step, and the boundary predicate is exactly the step output.
-- source:
--   Uniform entropy-based integer regional construction for the More Asymmetry matrix multiplication campaign, https://arxiv.org/html/2404.16349v2#S6 . This child isolates the dimension-25 boundary data matched to a given step; the five-copy step itself is a separate child.

import Definitions.Def_mme_entropy_regional_CW_recipe
open MME MME.ProfiledCW MME.RegionRealization
set_option autoImplicit false

theorem mme_entropy_regional_boundary_match : ∀ (lower : ℕ) (S : IntegerStep lower 2 (fun _ _ ↦ True)), ∃ (B : BoundaryEnd lower 2 S.output), B.a * B.b * B.c = 25 ∧ 1 ≤ B.a * B.b * B.c := by sorry
