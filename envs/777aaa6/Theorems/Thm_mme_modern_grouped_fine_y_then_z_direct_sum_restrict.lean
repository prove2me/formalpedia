-- Prove2me | Theorems.Thm_mme_modern_grouped_fine_y_then_z_direct_sum_restrict
-- name    : mme_modern_grouped_fine_y_then_z_direct_sum_restrict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-07T03:57:05.544162+00:00
-- url     : https://prove2.me/theorems/c23eb8b9-f09c-439b-8ce9-b4a8e390bf4c
-- title:
--   Grouped outer copies retain entire fine-block unions under sequential Y/Z ownership
-- statement:
--   Let $T$ be a three-tensor over a field, with finite mode bases and full fine-label maps. For each outer-copy owner $j$, choose an allowed set of labels in each mode, and let $B_j$ be the actual simultaneous basis projection of $T$ onto the entire union of those fine blocks. Suppose retained $Y$ labels are compatible only with their own owner, and every nonzero tensor coefficient retained by a mixed selection of owners makes its $Y$ label compatible with the $X$-selected owner. After those two owners coincide, assume the analogous supported $Z$ compatibility and uniqueness. Then
--
--   $$\bigoplus_j B_j\;\preceq\;T.$$
--
--   Here $\preceq$ is an actual mode-wise linear tensor restriction. All internal terms and shared variables within each $B_j$ are retained; uniqueness is required only between distinct outer-copy owners, not between fine-block triples inside a copy. Support is the actual coefficient support of $T$ in the specified product basis. This deterministic tensor-algebra result does not assert the existence of a large retained family, bound its holes, or certify a numerical value surplus.
-- source:
--   Derived grouped-copy linear-algebra realization of the sequential fine-Y then fine-Z ownership in Alman et al., More Asymmetry Yields Faster Matrix Multiplication, arXiv:2404.16349v2, Sections 5.3–5.5 (especially Claims 5.7, 5.10 and 5.12) and 6.3–6.5. https://arxiv.org/abs/2404.16349v2 . Uses the existing Proved generic actual mixed-mode-map direct-sum restriction theorem mme_tensor_family_direct_sum_restrict_of_mixed_maps. This is a source-faithful finite algebraic adapter, not a claim that the source-specific hash/compatibility counting or three-mode hole repair has been proved.

import Definitions.Def_mme_complete_split_profile_projection
import Definitions.Def_mme_tensor_rank
import Mathlib.LinearAlgebra.PiTensorProduct.Basis

open MME Module PiTensorProduct BigOperators

universe u v

set_option autoImplicit false

theorem mme_modern_grouped_fine_y_then_z_direct_sum_restrict
    {K : Type u} [Field K] (T : TensorObj K 3) {k : ℕ}
    {ι : Fin 3 → Type u} [∀ i, Fintype (ι i)]
    {Label : Fin 3 → Type v}
    (b : (i : Fin 3) → Basis (ι i) K (T.V i))
    (fineLabel : (i : Fin 3) → ι i → Label i)
    (allowed : Fin k → (i : Fin 3) → Label i → Prop)
    (compatibleY : Label 1 → Fin k → Prop)
    (compatibleZ : Label 2 → Fin k → Prop)
    (hYUnique : ∀ (j j' : Fin k) (y : Label 1),
      allowed j 1 y → compatibleY y j' → j' = j)
    (hSupportedY : ∀ (x : (i : Fin 3) → ι i) (js : Fin 3 → Fin k),
      (Basis.piTensorProduct b).repr T.t x ≠ 0 →
      (∀ i, allowed (js i) i (fineLabel i (x i))) →
      compatibleY (fineLabel 1 (x 1)) (js 0))
    (hZUnique : ∀ (j j' : Fin k) (z : Label 2),
      allowed j 2 z → compatibleZ z j' → j' = j)
    (hSupportedZ : ∀ (x : (i : Fin 3) → ι i) (js : Fin 3 → Fin k),
      (Basis.piTensorProduct b).repr T.t x ≠ 0 →
      (∀ i, allowed (js i) i (fineLabel i (x i))) →
      js 0 = js 1 →
      compatibleZ (fineLabel 2 (x 2)) (js 0)) :
    TensorObj.Restrict
      (TensorObj.bigAdd (fun j : Fin k ↦
        T.basisAllAllowedSubtensor b
          (fun i x ↦ allowed j i (fineLabel i x))))
      T := by
  sorry
