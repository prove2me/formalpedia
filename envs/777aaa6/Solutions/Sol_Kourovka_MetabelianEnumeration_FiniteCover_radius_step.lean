-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.FiniteCover.radius_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:16:19.838624+00:00
-- url     : https://prove2.me/submissions/148d1ef1-ee0d-43cc-a9c9-fce4242d6956

import Definitions.Def_Kourovka_Collection_CollectionRadius
import Definitions.Def_Kourovka_Covers_CertifiedRadius
import Definitions.Def_Kourovka_Modules_TamenessCompactness
import Definitions.Def_Kourovka_Covers_CoverSoundness
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_commute_polynomial_conjugate
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_abs_unitSign
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_blockWord_finRange
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_collection_radius
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_collection_radius_inverse
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_commute_conjugate_iff
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
import Theorems.Thm_Kourovka_MetabelianEnumeration_vector_radius_shrink
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
    (hk : 1 ≤ k) (C D ρ δ : ℝ)
    (hC : 0 < C) (hρk : 2 * (k : ℝ) < ρ) (hρD : 2 * (k : ℝ) * D < ρ)
    (hρC : C < ρ) (hρD2 : D ^ 2 < C * ρ)
    (hδ : 0 < δ) (hδC : δ ≤ C / 4) (hδk : δ < 1 / (2 * (k : ℝ)))
    (ht : ∀ i j, i < j → rightComm (t i) (t j) = A (data.designated i j))
    (hs : ∀ p q v, v ∈ ball ρ → Commute (A p) (conjugate (A q) (orderedWord t v)))
    (hp : ∀ i p, p ∈ data.polynomials → A i = polynomialWord t (A i) p)
    (hbound : ∀ p ∈ data.polynomials, ∀ term ∈ p.2, ‖euclidean term.1‖ ≤ D)
    (hdir : ∀ v : Lattice k, v ≠ 0 → ∃ p ∈ data.polynomials,
      ∀ term ∈ p.2, inner ℝ (euclidean v) (euclidean term.1) ≤ -C * ‖euclidean v‖) :
    ∀ p q v, v ∈ ball (ρ + δ) → Commute (A p) (conjugate (A q) (orderedWord t v)) := by
  intro p q v hv
  by_cases hv0 : v ∈ ball ρ
  · exact hs p q v hv0
  have hvge : ρ ≤ ‖euclidean v‖ := le_of_not_gt hv0
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hρ0 : 0 < ρ := by linarith
  have hvne : v ≠ 0 := by
    intro he
    have hzero : euclidean v = 0 := by ext i; simp [he, euclidean]
    rw [hzero, norm_zero] at hvge
    linarith
  obtain ⟨poly, hpoly, hdot⟩ := hdir v hvne
  have hshort : ∀ term ∈ poly.2, ‖euclidean term.1‖ ≤ ρ / (2 * k) := by
    intro term hterm
    exact (hbound poly hpoly term hterm).trans
      ((le_div_iff₀ (by positivity : (0 : ℝ) < 2 * k)).mpr (by nlinarith))
  have hsum : ∀ term ∈ poly.2, ‖euclidean (term.1 + v)‖ < ρ := by
    intro term hterm
    have hu := hbound poly hpoly term hterm
    have hD0 : 0 ≤ D := (norm_nonneg _).trans hu
    have h := vector_radius_shrink (euclidean v) (euclidean term.1) C D ρ δ
      hC hρC hρD2 hδ hδC hvge hv (by nlinarith [norm_nonneg (euclidean term.1)])
      (hdot term hterm)
    simpa only [euclidean_add, add_comm] using h
  have hv' : ‖euclidean v‖ < ρ + 1 / (2 * k) := lt_of_lt_of_le hv (by linarith)
  cases hsign : poly.1
  · apply (commute_conjugate_iff _ _ _).mpr
    apply Commute.symm
    rw [hp p poly hpoly]
    apply commute_polynomial_conjugate
    intro term hterm
    simp only [hsign, Bool.false_eq_true, ↓reduceIte]
    exact collection_radius_inverse A t data.designated hk ρ hρk ht hs q p term.1 v
      (hshort term hterm) hv' (hsum term hterm)
  · rw [hp q poly hpoly]
    apply commute_polynomial_conjugate
    intro term hterm
    simp only [hsign, ↓reduceIte]
    exact collection_radius A t data.designated hk ρ hρk ht hs p q term.1 v
      (hshort term hterm) hv' (hsum term hterm)
end Kourovka.MetabelianEnumeration.FiniteCover
