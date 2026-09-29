-- Prove2me | Theorems.Thm_mme_dwz_q6_common_halving_union_matrix_cardinality_restriction
-- name    : mme_dwz_q6_common_halving_union_matrix_cardinality_restriction
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T04:10:12.613046+00:00
-- url     : https://prove2.me/theorems/74983c8d-99e4-4f6f-96fb-1f3ba7947f74
-- title:
--   Common-halving word unions extract a matrix block from the restricted component pair
-- statement:
--   Let $K$ be a field and let $s\in\{13,14\}$ be one of the DWZ table components. Write $N=c_s m$. Let a primary hash family of length $2N$ admit a common balanced XY halving. Let $X$ be the set of third-coordinate words of the first oriented matrix power whose inverse trace labels match the first X half of at least one family entry. Define $Y$ using the second Y half and the other orientation. Then the literal restricted component pair admits the restriction
--   $$\langle |X|,1,|Y|\rangle\preceq \operatorname{componentPairRestricted}_K(s,m).$$
--   The two unions are selected independently, so all pairs in $X\times Y$ contribute to the extracted block. The dimensions count distinct retained words, including any numeric label multiplicities, without assuming that different family entries have distinct half-patterns.
-- source:
--   Composition of the common-halving union trace restriction with Cartesian matrix-word block extraction.

import Theorems.Thm_mme_dwz_q6_common_halving_union_trace_projection_restriction
import Theorems.Thm_mme_paired_matrix_cartesian_word_projection_extraction

open MME MME.DWZComponentRestriction PiTensorProduct Module TensorProduct BigOperators
universe u
set_option autoImplicit false

theorem mme_dwz_q6_common_halving_union_matrix_cardinality_restriction
    {K : Type u} [Field K] {N L G A H : ℕ}
    (s : Fin 15) (hs : s = 13 ∨ s = 14) (m : ℕ)
    (hN : N = DWZTable2Counts.component s * m)
    (family : CWQ6PrimaryHashFamily N L G A H)
    (halving : family.CommonBalancedXYHalving) :
    let h0 := fun w : PowIndex (ULift.{u} (Fin 1 × Fin (6 + 6))) N ↦
      PowIndex.ofFun N (fun r ↦
        (⟨finSumFinEquiv.symm (PowIndex.get N w r).down.2⟩ : ULift.{u} (Fin 6 ⊕ Fin 6)))
    let h1 := fun w : PowIndex (ULift.{u} (Fin (6 + 6) × Fin 1)) N ↦
      PowIndex.ofFun N (fun r ↦
        (⟨Sum.swap (finSumFinEquiv.symm (PowIndex.get N w r).down.1)⟩ :
          ULift.{u} (Fin 6 ⊕ Fin 6)))
    let grade : ULift.{u} (Fin 6 ⊕ Fin 6) → Fin 3 :=
      fun x ↦ Sum.elim (fun _ ↦ 0) (fun _ ↦ 1) x.down
    let keepX := fun w : PowIndex (ULift.{u} (Fin 1 × Fin (6 + 6))) N ↦
      ∃ p : Fin A × Fin H, ∀ r,
        grade (PowIndex.get N (h0 w) r) =
          (family.entry p).val 0 (halving.position (Sum.inl r))
    let keepY := fun w : PowIndex (ULift.{u} (Fin (6 + 6) × Fin 1)) N ↦
      ∃ p : Fin A × Fin H, ∀ r,
        grade (PowIndex.get N (h1 w) r) =
          (family.entry p).val 1 (halving.position (Sum.inr r))
    letI : DecidablePred keepX := Classical.decPred _
    letI : DecidablePred keepY := Classical.decPred _
    TensorObj.Restrict
      (MMObj K (Fintype.card {x // keepX x}) 1 (Fintype.card {y // keepY y}))
      (componentPairRestricted K s m) := by sorry
