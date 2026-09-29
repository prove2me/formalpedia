-- Prove2me | solution 1 for mme_dwz_q6_common_halving_trace_matrix_volume_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T04:21:29.491792+00:00
-- url     : https://prove2.me/submissions/a95cb1c4-1551-45c0-979a-f45f0e98a436

import Theorems.Thm_mme_dwz_q6_common_halving_union_matrix_pattern_restriction
import Theorems.Thm_mme_CW_q6_common_halving_fiber_half_pattern_product_bound

open MME MME.DWZComponentRestriction
universe u
set_option autoImplicit false

/-- A nonempty color set yields a matrix block whose volume includes the
entire fiber size and the independent numeric labels in both halves. -/
theorem solution
    {K : Type u} [Field K] {N L G A H : ℕ}
    (s : Fin 15) (hs : s = 13 ∨ s = 14) (m : ℕ)
    (hN : N = DWZTable2Counts.component s * m)
    (family : CWQ6PrimaryHashFamily N L G A H)
    (halving : family.CommonBalancedXYHalving) (a : Fin A) :
    ∃ n p : ℕ, TensorObj.Restrict (MMObj K n 1 p) (componentPairRestricted K s m) ∧
      H * 6 ^ (2 * N) ≤ n * p := by
  classical
  let x := fun p : Fin A × Fin H ↦
    fun r : Fin N ↦ (family.entry p).val 0 (halving.position (Sum.inl r))
  let y := fun p : Fin A × Fin H ↦
    fun r : Fin N ↦ (family.entry p).val 1 (halving.position (Sum.inr r))
  let PX := Finset.univ.image x
  let PY := Finset.univ.image y
  let QX := Finset.univ.image (fun h : Fin H ↦ x (a,h))
  let QY := Finset.univ.image (fun h : Fin H ↦ y (a,h))
  have sx : QX ⊆ PX := by
    intro b hb
    obtain ⟨h, _, rfl⟩ := Finset.mem_image.mp hb
    exact Finset.mem_image.mpr ⟨(a,h), Finset.mem_univ _, rfl⟩
  have sy : QY ⊆ PY := by
    intro b hb
    obtain ⟨h, _, rfl⟩ := Finset.mem_image.mp hb
    exact Finset.mem_image.mpr ⟨(a,h), Finset.mem_univ _, rfl⟩
  have hf : H ≤ QX.card * QY.card :=
    mme_CW_q6_common_halving_fiber_half_pattern_product_bound family halving a
  have hp : H ≤ PX.card * PY.card :=
    hf.trans (Nat.mul_le_mul (Finset.card_le_card sx) (Finset.card_le_card sy))
  refine ⟨PX.card * 6 ^ N, PY.card * 6 ^ N, ?_, ?_⟩
  · exact mme_dwz_q6_common_halving_union_matrix_pattern_restriction
      (K := K) s hs m hN family halving
  · calc
      H * 6 ^ (2 * N) ≤ (PX.card * PY.card) * 6 ^ (2 * N) :=
        Nat.mul_le_mul_right _ hp
      _ = (PX.card * 6 ^ N) * (PY.card * 6 ^ N) := by
        rw [two_mul, pow_add]
        ring

#print axioms solution
