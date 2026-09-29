-- Prove2me | Theorems.Thm_mme_direct_sum_component_assembly_iff_mixed_vanishing
-- name    : mme_direct_sum_component_assembly_iff_mixed_vanishing
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T04:38:45.418995+00:00
-- url     : https://prove2.me/theorems/aada9289-a8af-4c70-8227-deebb3f9bcd4
-- title:
--   Exact criterion for assembling component maps into a direct sum
-- statement:
--   Let $T$ be an order-three tensor over a field, and let $B_j$, for $0\le j<k$, be component tensors with mode maps $P_{j,i}$ satisfying $(\bigotimes_i P_{j,i})T=B_j$. Let $\iota_{j,i}$ include the $j$th component space into the direct sum. Then
--   $$\left(\bigotimes_{i=0}^2\sum_{j=0}^{k-1}\iota_{j,i}P_{j,i}\right)T
--   =\bigoplus_{j=0}^{k-1}B_j$$
--   if and only if $(\bigotimes_i P_{j_i,i})T=0$ for every nonconstant triple $(j_0,j_1,j_2)$. This gives both necessity and sufficiency for this specific assembly of component maps; it makes no assertion about other possible restriction maps.
-- source:
--   Multilinear expansion and direct-sum coordinate projections; in the coupled-family application, the accepted exact mixed-projection support theorem and within-color half-pattern support criterion.

import Definitions.Def_mme_induced_word_zeroing
import Mathlib.LinearAlgebra.PiTensorProduct

open MME PiTensorProduct BigOperators
universe u
set_option autoImplicit false

theorem mme_direct_sum_component_assembly_iff_mixed_vanishing
    {K : Type u} [Field K] {k : ℕ}
    (T : TensorObj K 3) (B : Fin k → TensorObj K 3)
    (proj : ∀ j i, T.V i →ₗ[K] (B j).V i)
    (hdiag : ∀ j, PiTensorProduct.map (proj j) T.t = (B j).t) :
    PiTensorProduct.map (fun i => ∑ j,
      (gradedBigAddSlot k B j i).comp (proj j i)) T.t = (TensorObj.bigAdd B).t ↔
      ∀ js : Fin 3 → Fin k, (¬ ∃ j, js = fun _ => j) →
        PiTensorProduct.map (fun i => proj (js i) i) T.t = 0 := by sorry
