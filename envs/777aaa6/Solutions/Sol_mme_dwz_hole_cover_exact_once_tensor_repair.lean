-- Prove2me | solution 1 for mme_dwz_hole_cover_exact_once_tensor_repair
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T09:16:02.687301+00:00
-- url     : https://prove2.me/submissions/d4eff9d8-9c10-4c16-8c6e-f8efb16da7a5

import Theorems.Thm_mme_dwz_hole_lemma_cover_core
import Theorems.Thm_mme_bigAdd_map_sum_restrict

/-!
# Tensor realization of the Hole-Lemma cover

The finite cover chooses shuffled broken copies.  The remaining source-specific
input is deliberately a family of actual modewise maps.  Those maps leave the
two shared X/Y shuffle maps unchanged and use the Z map to keep exactly the
blocks assigned to that copy.  Their tensor equations, rather than a scalar
cardinality assertion, certify that each target monomial is realized exactly
once.
-/

open BigOperators Finset
open MME MME.DWZSquare PiTensorProduct

universe u v

set_option autoImplicit false
set_option warningAsError true

/-- A Hole-Lemma cover repairs a finite family of broken tensor objects once
the concrete shuffles and Z-only owner projections are realized by modewise
linear maps.  The conclusion is a genuine restriction from the direct sum of
broken sources onto the complete standard block sum. -/
theorem solution
    {K : Type u} [Field K]
    {s : ℕ}
    {W : Fin 3 → Type u}
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    [∀ i, Module.Finite K (W i)]
    {Block : Type u} {Shuffle : Type v}
    [Fintype Block] [DecidableEq Block] [Nonempty Block]
    [Fintype Shuffle] [DecidableEq Shuffle] [Nonempty Shuffle]
    (system : AvailableBlockShuffle Block Shuffle)
    (N ell : ℕ) (hN : 0 < N) (hell : 0 < ell)
    (copies : Fin s → BrokenBlockCopy Block)
    (hcard : Fintype.card Block ≤ 2 ^ (N * ell))
    (hsum : ((N * ell + 1 : ℕ) : ℝ) ≤
      ∑ t : Fin s, nonholeFraction (copies t))
    (source : Fin s → TensorObj K 3)
    (blockTensor : Block → PiTensorProduct K W)
    (shuffleMap : (Fin s → Shuffle) →
      ∀ t i, (source t).V i →ₗ[K] W i)
    (realizeOwned :
      ∀ (shuffles : Fin s → Shuffle) (owner : Block → Fin s),
        (∀ block : Block,
          (system.move (shuffles (owner block))).symm block ∈
            (copies (owner block)).nonholes) →
        ∃ f : ∀ t i, (source t).V i →ₗ[K] W i,
          (∀ t, f t 0 = shuffleMap shuffles t 0) ∧
          (∀ t, f t 1 = shuffleMap shuffles t 1) ∧
          ∀ t,
            PiTensorProduct.map (f t) (source t).t =
              ∑ block : Block,
                if t = owner block then blockTensor block else 0) :
    ∃ (shuffles : Fin s → Shuffle) (owner : Block → Fin s)
        (f : ∀ t i, (source t).V i →ₗ[K] W i),
      (∀ block : Block, ∃ t : Fin s,
        (system.move (shuffles t)).symm block ∈ (copies t).nonholes) ∧
      (∀ block : Block,
        (system.move (shuffles (owner block))).symm block ∈
          (copies (owner block)).nonholes) ∧
      (∀ t, f t 0 = shuffleMap shuffles t 0) ∧
      (∀ t, f t 1 = shuffleMap shuffles t 1) ∧
      (∀ t,
        PiTensorProduct.map (f t) (source t).t =
          ∑ block : Block,
            if t = owner block then blockTensor block else 0) ∧
      TensorObj.Restrict
        ({ V := W
           t := ∑ block : Block, blockTensor block } : TensorObj K 3)
        (TensorObj.bigAdd source) := by
  classical
  obtain ⟨shuffles, hcover⟩ := mme_dwz_hole_lemma_cover_core
    system N ell s hN hell copies hcard hsum
  let owner : Block → Fin s := fun block ↦ Classical.choose (hcover block)
  have howner : ∀ block : Block,
      (system.move (shuffles (owner block))).symm block ∈
        (copies (owner block)).nonholes := by
    intro block
    exact Classical.choose_spec (hcover block)
  obtain ⟨f, hfX, hfY, hfTensor⟩ := realizeOwned shuffles owner howner
  refine ⟨shuffles, owner, f, hcover, howner, hfX, hfY, hfTensor, ?_⟩
  have hexact :
      (∑ t : Fin s, ∑ block : Block,
        if t = owner block then blockTensor block else 0) =
        ∑ block : Block, blockTensor block := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro block _
    simp
  have hmapped :
      (∑ t : Fin s,
        PiTensorProduct.map (f t) (source t).t) =
        ∑ block : Block, blockTensor block := by
    calc
      (∑ t : Fin s, PiTensorProduct.map (f t) (source t).t) =
          ∑ t : Fin s, ∑ block : Block,
            if t = owner block then blockTensor block else 0 := by
              exact Finset.sum_congr rfl (fun t _ ↦ hfTensor t)
      _ = ∑ block : Block, blockTensor block := hexact
  have hfold := mme_bigAdd_map_sum_restrict source f
  simpa only [hmapped] using hfold

