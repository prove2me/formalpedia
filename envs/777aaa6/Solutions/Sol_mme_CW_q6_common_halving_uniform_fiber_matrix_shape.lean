-- Prove2me | solution 1 for mme_CW_q6_common_halving_uniform_fiber_matrix_shape
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T04:29:24.420208+00:00
-- url     : https://prove2.me/submissions/33eeeea4-c15f-407c-9bfb-d934d200bb14

import Theorems.Thm_mme_CW_q6_common_halving_paired_oriented_component_certificate

open MME MME.PairedOrientedPackaging BigOperators
universe u
set_option autoImplicit false

/-- The untraced middle dimension retains a factor of six for each mixed
position; the product of the two outer dimensions accounts for all positions. -/
theorem mme_CW_q6_paired_component_middle_and_outer_dimensions
    {N L G A H : ℕ} (family : CWQ6PrimaryHashFamily N L G A H)
    (halving : family.CommonBalancedXYHalving) (p : Fin A × Fin H) :
    componentN family halving p = 6 ^ (2 * G) ∧
    componentM family halving p * componentP family halving p = 6 ^ (2 * N) := by
  constructor
  · let f : Fin (2 * N) → ℕ := fun j ↦
      if (family.entry p).val 2 j = 2 then 6 else 1
    have he : (∏ r : Fin N, f (halving.position (Sum.inl r))) *
        (∏ r : Fin N, f (halving.position (Sum.inr r))) = ∏ j : Fin (2 * N), f j := by
      calc
        _ = ∏ r : Fin N ⊕ Fin N, f (halving.position r) :=
          (Fintype.prod_sum_type (fun r ↦ f (halving.position r))).symm
        _ = _ := halving.position.prod_comp f
    change (∏ r : Fin N, f (halving.position (Sum.inl r))) *
      (∏ r : Fin N, f (halving.position (Sum.inr r))) = _
    rw [he]
    dsimp only [f]
    rw [← Finset.prod_filter, Finset.prod_const, (family.entry p).property.2 2 2]
    rfl
  · have hleft (t : Fin 3 → Fin 3) : localN t * localM t = 6 := by
      unfold localN localM
      split_ifs <;> norm_num
    have hright (t : Fin 3 → Fin 3) : localP t * localN t = 6 := by
      unfold localP localN
      split_ifs <;> norm_num
    calc
      componentM family halving p * componentP family halving p =
          (∏ r : Fin N, localN (leftType family halving p r) *
            localM (leftType family halving p r)) *
          (∏ r : Fin N, localP (rightType family halving p r) *
            localN (rightType family halving p r)) := by
        simp only [componentM, componentP, Finset.prod_mul_distrib]
        ac_rfl
      _ = 6 ^ N * 6 ^ N := by simp only [hleft, hright]; simp
      _ = 6 ^ (2 * N) := by rw [two_mul, pow_add]

/-- All matrix dimensions are constant within a color because their local
factors depend only on its common third-coordinate grade word. -/
theorem mme_CW_q6_paired_component_dimensions_same_fiber
    {N L G A H : ℕ} (family : CWQ6PrimaryHashFamily N L G A H)
    (halving : family.CommonBalancedXYHalving) (a : Fin A) (h k : Fin H) :
    componentM family halving (a,h) = componentM family halving (a,k) ∧
    componentN family halving (a,h) = componentN family halving (a,k) ∧
    componentP family halving (a,h) = componentP family halving (a,k) := by
  have hz : ∀ j, (family.entry (a,h)).val 2 j = (family.entry (a,k)).val 2 j :=
    fun j ↦ congrFun (family.zSameFiber a h k) j
  simp only [componentM, componentN, componentP, localM, localN, localP,
    leftType, rightType, hz]
  exact ⟨rfl, rfl, rfl⟩

/-- Every untraced component in a fixed color has the same matrix shape,
with middle dimension exactly `6 ^ (2 * G)` and outer product `6 ^ (2 * N)`. -/
theorem solution
    {K : Type u} [Field K] {N L G A H : ℕ}
    (family : CWQ6PrimaryHashFamily N L G A H)
    (halving : family.CommonBalancedXYHalving) (a : Fin A) :
    ∃ m p : ℕ, m * p = 6 ^ (2 * N) ∧
      ∀ h : Fin H, TensorObj.Isomorphic (MMObj K m (6 ^ (2 * G)) p)
        (componentObj (K := K) family halving (a,h)) := by
  let h0 : Fin H := ⟨0, family.hHpos⟩
  refine ⟨componentM family halving (a,h0), componentP family halving (a,h0),
    (mme_CW_q6_paired_component_middle_and_outer_dimensions family halving (a,h0)).2, ?_⟩
  intro h
  have hi := (mme_CW_q6_common_halving_paired_oriented_component_certificate
    (K := K) family halving (a,h)).1
  obtain ⟨hm, _, hp⟩ := mme_CW_q6_paired_component_dimensions_same_fiber
    family halving a h h0
  have hn := (mme_CW_q6_paired_component_middle_and_outer_dimensions
    family halving (a,h)).1
  rw [hm, hn, hp] at hi
  exact hi

#print axioms solution
