-- Prove2me | Theorems.Thm_mme_profiled_exact_step_output_is_stage_template_cell_product
-- name    : mme_profiled_exact_step_output_is_stage_template_cell_product
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-20T02:20:17.246631+00:00
-- url     : https://prove2.me/theorems/def43b13-3e5e-4c0a-9aeb-e58785bf4659
-- title:
--   Exact-step output projection is the stage template, and its cell product restricts from it
-- statement:
--   Let $E$ be an exact profiled-CW step of level $\ell$ on flat words of length $N$, for a source predicate $P$. Its stage carries a reference address, a position equivalence, and per-mode cell word profiles $\mu$; its output predicate keeps precisely the words that are *graded* at the reference address and *useful* for $\mu$.
--
--   Two statements are asserted.
--
--   **The output projection is the stage template.**
--
--   $$\mathrm{tensor}_K\big(E.\mathrm{output}\big) \;=\; E.\mathrm{stage}.\mathrm{template}\,K .$$
--
--   Both sides are all-mode projections of $\mathrm{CW}_5^{\otimes N}$ along the same canonical word basis. On the left the filter is written on flat words of length $N$; on the right it is written on the cells of the block decomposition, with shape $c \mapsto (c_2)_i$. They agree once the flat length is transported along $L\cdot 2^{\ell-1} = N$: the `Graded` condition is the per-cell grade condition of `allowed`, since the grade of a complete word is the sum of its letters, and the usefulness conditions are literally the same. This is an equality of tensors, not merely a restriction, so it may be rewritten in either direction and under further constructions.
--
--   **The cell product restricts from it.** For any partition $D$ of the cell map,
--
--   $$\bigotimes_{j < D.\mathrm{parts}} D.\mathrm{piece}_j \;\trianglelefteq\; \mathrm{tensor}_K\big(E.\mathrm{output}\big),$$
--
--   which is the accepted intact-template cell-product restriction transported along the same equality.
--
--   The purpose is to connect the exact-step machinery, whose conclusions are phrased with `ProfiledCW.tensor` on flat words, to the cell-wise template phrasing used by the recursive assembly interface, so that each cell piece can then be given its own value. No asymptotic or numerical claim is made.
-- source:
--   Bridge between the profiled-CW exact-step conclusions and the cell-template phrasing of the recursive assembly interface, for More Asymmetry Yields Faster Matrix Multiplication, https://arxiv.org/html/2404.16349v2#S6 . The cell-product half is the accepted mme_recursive_yz_actual_cell_product_restriction transported along the flat-word length equation. Supporting lemma only: no asymptotic or numerical claim.

import Definitions.Def_mme_recursive_profiled_CW_data
import Definitions.Def_mme_recursive_yz_cell_partition
import Definitions.Def_mme_recursive_yz_stage_certificate

open MME MME.TensorObj MME.RecursiveYZ MME.RecursiveYZ.CWCells MME.ProfiledCW MME.CompleteSplit
open scoped Classical
universe u
set_option autoImplicit false

theorem mme_profiled_exact_step_output_is_stage_template_cell_product {K : Type u} [Field K] {ell N : ℕ} {P : ProfiledCW.Predicate N}
    (E : ProfiledCW.ExactStep ell N P)
    (D : Partition (fullCell E.stage.total E.stage.reference)) :
    ProfiledCW.tensor K E.output = E.stage.template K ∧
    Restrict
      (kronFin D.parts (D.piece K 5 E.stage.ell (fun c i ↦ (c.2.val i).val) E.stage.mu))
      (ProfiledCW.tensor K E.output) := by sorry
