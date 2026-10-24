-- Prove2me | solution 1 for NoUniversalFSigma.no_universal_fsigma
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-23T09:43:49.578076+00:00
-- url     : https://prove2.me/submissions/4f0be5bb-d69e-4a91-b730-fdb1dcb2f0b8

import Theorems.Thm_NoUniversalFSigma_theorem1_1
import Mathlib.Analysis.InnerProductSpace.l2Space

open Set TopologicalSpace

private theorem realL2_separable : SeparableSpace NoUniversalFSigma.RealL2 := by
  let b : HilbertBasis ℕ ℝ NoUniversalFSigma.RealL2 := default
  have hs : IsSeparable (Submodule.span ℝ (range b) : Set NoUniversalFSigma.RealL2) :=
    (Set.countable_range b).isSeparable.span
  have hc := hs.closure
  have heq : closure (Submodule.span ℝ (range b) : Set NoUniversalFSigma.RealL2) = Set.univ := by
    change ((Submodule.span ℝ (range b)).topologicalClosure : Set NoUniversalFSigma.RealL2) = Set.univ
    rw [b.dense_span]
    rfl
  rw [heq] at hc
  exact isSeparable_univ_iff.mp hc

theorem solution
    {Y : Type} [TopologicalSpace Y] [PolishSpace Y] :
    ¬ ∃ F : Setoid Y,
      NoUniversalFSigma.IsFSigmaRelation F.r ∧ NoUniversalFSigma.IsUniversalFSigma F.r := by
  rintro ⟨F, hF, hUniversal⟩
  letI : SeparableSpace NoUniversalFSigma.RealL2 := realL2_separable
  obtain ⟨H, _, hCoset, hnon⟩ := NoUniversalFSigma.theorem1_1 F hF
  obtain ⟨f, hf, hred⟩ := hUniversal NoUniversalFSigma.RealL2
    (NoUniversalFSigma.CosetRelation H) (NoUniversalFSigma.cosetRelation_equivalence H) hCoset
  exact hnon ⟨f, NoUniversalFSigma.isBorelMeasurable_isBaireMeasurable hf, hred⟩

#print axioms solution
