-- Prove2me | solution 1 for PermutationDichotomy.attentionAlgebra_separatesPoints
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-16T01:37:26.234872+00:00
-- url     : https://prove2.me/submissions/371df1df-a25c-4591-907c-1c9245d733fc

/-
# `PermutationDichotomy.attentionAlgebra_separatesPoints`
Target `f35c6d5f-3da7-484d-b047-29654a18d2a6` (Open, not deprecated, at submission time).

Reduction to the Proved platform node `ContinuousUniversality.attentionAlgebra_separatesPoints`
(`d3697fb7-5063-4aad-9912-9f77ab86eb05`). The two namespaces declare byte-identical copies of
`Seq`, `readoutCM` and `attentionAlgebra`, so they are distinct constants denoting the same
construction. The bridge identifies them; it is restated inline here because a submission may
never import another `Solutions` module.

`#print axioms solution` reports `sorryAx` from the imported mirror alone; the audit module
`Solutions/AxFree_dup_f35c6d5f.lean` binds that statement as a hypothesis and rebuilds the proof.
-/
import Mathlib
import Definitions.Def_MachineLearning_TransformerUniversality_PermutationDichotomy
import Theorems.Thm_ContinuousUniversality_attentionAlgebra_separatesPoints

set_option autoImplicit false

namespace DupBridge

theorem readoutCM_eq {ι κ : Type*} [Fintype ι] [Fintype κ] (w : ι → κ → ℝ) :
    PermutationDichotomy.readoutCM w = ContinuousUniversality.readoutCM w := by
  first
  | rfl
  | · ext y
      simp [PermutationDichotomy.readoutCM, ContinuousUniversality.readoutCM]

theorem attentionAlgebra_eq (ι κ : Type*) [Fintype ι] [Fintype κ] :
    PermutationDichotomy.attentionAlgebra ι κ = ContinuousUniversality.attentionAlgebra ι κ := by
  first
  | rfl
  | · unfold PermutationDichotomy.attentionAlgebra ContinuousUniversality.attentionAlgebra
      congr 1
      ext g
      constructor
      · rintro ⟨w, rfl⟩; exact ⟨w, (readoutCM_eq w).symm⟩
      · rintro ⟨w, rfl⟩; exact ⟨w, readoutCM_eq w⟩

end DupBridge

open PermutationDichotomy in
/-- **The target, verbatim.** Reduction to the Proved node `d3697fb7`. -/
theorem solution {ι κ : Type*} [Fintype ι] [Fintype κ] :
    (attentionAlgebra ι κ).SeparatesPoints := by
  first
  | exact ContinuousUniversality.attentionAlgebra_separatesPoints
  | · rw [DupBridge.attentionAlgebra_eq]
      exact ContinuousUniversality.attentionAlgebra_separatesPoints
