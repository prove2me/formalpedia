-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.FiniteCover.all_ordered_commute
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:17:19.588338+00:00
-- url     : https://prove2.me/submissions/35b2f3d4-d686-4275-9ac1-4fa0e5fddad8

import Definitions.Def_Kourovka_Collection_CollectionRadius
import Definitions.Def_Kourovka_Covers_CertifiedRadius
import Definitions.Def_Kourovka_Modules_TamenessCompactness
import Definitions.Def_Kourovka_Covers_CoverSoundness
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_radius_step
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_abs_unitSign
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_blockWord_finRange
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_conjugate_one
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_euclidean_add
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_euclidean_neg
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_euclidean_norm_abs
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_lower_shift
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_neg_mem_ball
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_not_precedes_self
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_orderedWord_zero
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_raise_lower
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_raise_shift
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_raise_snoc_castSucc
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_raise_snoc_last
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_shiftList_finRange
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_shiftList_nil
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_shift_zero
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.abs_unitSign
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.blockWord_finRange
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.conjugate_one
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.euclidean_add
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.euclidean_neg
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.euclidean_norm_abs
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.lower_shift
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.neg_mem_ball
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.not_precedes_self
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.orderedWord_zero
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.raise_lower
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.raise_shift
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.raise_snoc_castSucc
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.raise_snoc_last
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.shiftList_finRange
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.shiftList_nil
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.shift_zero



set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FiniteCover
open Collection
variable {G : Type*} [Group G]
namespace Kourovka.MetabelianEnumeration.FiniteCover
theorem _root_.solution {k a : ℕ} (data : Datum k a) (t : Fin k → G) (A : Fin a → G)
    (hk : 1 ≤ k) (C D R δ : ℝ)
    (hC : 0 < C) (hRk : 2 * (k : ℝ) < R) (hRD : 2 * (k : ℝ) * D < R)
    (hRC : C < R) (hRD2 : D ^ 2 < C * R)
    (hδ : 0 < δ) (hδC : δ ≤ C / 4) (hδk : δ < 1 / (2 * (k : ℝ)))
    (ht : ∀ i j, i < j → rightComm (t i) (t j) = A (data.designated i j))
    (hs : ∀ p q v, v ∈ ball R → Commute (A p) (conjugate (A q) (orderedWord t v)))
    (hp : ∀ i p, p ∈ data.polynomials → A i = polynomialWord t (A i) p)
    (hbound : ∀ p ∈ data.polynomials, ∀ term ∈ p.2, ‖euclidean term.1‖ ≤ D)
    (hdir : ∀ v : Lattice k, v ≠ 0 → ∃ p ∈ data.polynomials,
      ∀ term ∈ p.2, inner ℝ (euclidean v) (euclidean term.1) ≤ -C * ‖euclidean v‖) :
    ∀ p q v, Commute (A p) (conjugate (A q) (orderedWord t v)) := by
  have hstep : ∀ n : ℕ, ∀ p q v, v ∈ ball (R + n * δ) →
      Commute (A p) (conjugate (A q) (orderedWord t v)) := by
    intro n
    induction n with
    | zero => simpa using hs
    | succ n ih =>
      have hn : 0 ≤ (n : ℝ) * δ := mul_nonneg (Nat.cast_nonneg n) hδ.le
      have h := radius_step data t A hk C D (R + n * δ) δ hC
        (by linarith) (by linarith) (by linarith)
        (by nlinarith [mul_nonneg hC.le hn]) hδ hδC hδk ht ih hp hbound hdir
      simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_assoc] using h
  intro p q v
  obtain ⟨n, hn⟩ := exists_nat_gt ((‖euclidean v‖ - R) / δ)
  exact hstep n p q v (by
    change ‖euclidean v‖ < R + n * δ
    have := (div_lt_iff₀ hδ).mp hn
    linarith)
end Kourovka.MetabelianEnumeration.FiniteCover
