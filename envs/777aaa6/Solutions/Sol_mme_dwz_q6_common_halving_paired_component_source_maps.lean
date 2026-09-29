-- Prove2me | solution 1 for mme_dwz_q6_common_halving_paired_component_source_maps
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T01:02:19.56699+00:00
-- url     : https://prove2.me/submissions/c222a8da-70fa-4f39-8f28-37b6c2ea2e2e

import Theorems.Thm_mme_CW_q6_paired_oriented_componentProj_third_basis_vanishing
import Theorems.Thm_mme_dwz_q6_canonical_121_211_paired_powered_basis_labelled_source_router
import Theorems.Thm_mme_dwz_q6_121_211_common_halving_disallowed_word_mismatches_halves

open MME MME.PairedOrientedPackaging MME.DWZComponentRestriction
open Module TensorProduct
universe u
set_option autoImplicit false

/-- The canonical paired source maps are compatible with the forbidden-word
vanishing required by every retained component projection. -/
theorem solution
    {K : Type u} [Field K] {N L G A H : ℕ}
    (s : Fin 15) (hs : s = 13 ∨ s = 14) (m : ℕ)
    (hN : N = MME.DWZTable2Counts.component s * m)
    (family : CWQ6PrimaryHashFamily N L G A H)
    (halving : family.CommonBalancedXYHalving) :
    ∃ maps : ∀ i : Fin 3,
        (TensorObj.kron
          ((canonicalComponentBlock K (13 : Fin 15)).kronPow N)
          ((canonicalComponentBlock K (14 : Fin 15)).kronPow N)).V i →ₗ[K]
        (TensorObj.kron
          ((TensorObj.permObj (cyclicPerm.trans cyclicPerm)
            (coupledObj K 6)).kronPow N)
          ((TensorObj.permObj cyclicPerm (coupledObj K 6)).kronPow N)).V i,
      PiTensorProduct.map maps
          (TensorObj.kron
            ((canonicalComponentBlock K (13 : Fin 15)).kronPow N)
            ((canonicalComponentBlock K (14 : Fin 15)).kronPow N)).t =
        (TensorObj.kron
          ((TensorObj.permObj (cyclicPerm.trans cyclicPerm)
            (coupledObj K 6)).kronPow N)
          ((TensorObj.permObj cyclicPerm (coupledObj K 6)).kronPow N)).t ∧
      ∀ (w13 w14 : PowIndex (LiftedCoarsePair.{u} 6 1) N),
        ((¬ ∀ a : Fin 3,
          Fintype.card {r : Fin N // (PowIndex.get N w13 r).leftGrade = a} =
            MME.DWZTable2Counts.split s a * m) ∨
         (¬ ∀ a : Fin 3,
          Fintype.card {r : Fin N // (PowIndex.get N w14 r).leftGrade = a} =
            MME.DWZTable2Counts.split s a * m)) →
        ∀ p : Fin A × Fin H,
          ((componentProj (K := K) family halving p 2).comp (maps 2))
            (kronPowModeBasis (canonicalComponentBlock K (13 : Fin 15)) 2
                (canonicalComponentZBasis K (13 : Fin 15)) N w13 ⊗ₜ[K]
              kronPowModeBasis (canonicalComponentBlock K (14 : Fin 15)) 2
                (canonicalComponentZBasis K (14 : Fin 15)) N w14) = 0 := by
  obtain ⟨coord, hcoord, maps, htensor, hbasis⟩ :=
    mme_dwz_q6_canonical_121_211_paired_powered_basis_labelled_source_router K N
  refine ⟨maps, htensor, ?_⟩
  intro w13 w14 hbad p
  rw [LinearMap.comp_apply, hbasis]
  apply mme_CW_q6_paired_oriented_componentProj_third_basis_vanishing
  have hmismatch := mme_dwz_q6_121_211_common_halving_disallowed_word_mismatches_halves
    s hs m hN family halving coord hcoord
  rcases hbad with h13 | h14
  · obtain ⟨r, hr⟩ := hmismatch.1 w13 h13 p
    exact Or.inl ⟨r, by simpa using hr⟩
  · obtain ⟨r, hr⟩ := hmismatch.2 w14 h14 p
    exact Or.inr ⟨r, by simpa using hr⟩
