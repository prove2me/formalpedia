-- Prove2me | solution 1 for mme_dwz_q5_global_node_weighted_assembly
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-20T17:48:48.674207+00:00
-- url     : https://prove2.me/submissions/14cd4df6-4a7a-4d5b-a121-c0ea40b414cb

import Definitions.Def_mme_dwz_prescribed_z_finite_weighted_node_assembly_from_length
import Definitions.Def_mme_dwz_q5_global_asymptotic_data
import Definitions.Def_mme_complete_split_cw_fourth_labels
import Definitions.Def_mme_CW_2376_address_block
import Theorems.Thm_mme_dwz_q5_actual_standard_products_asymptotic_rate
import Theorems.Thm_mme_dwz_q5_exact_global_profile_certificate
import Theorems.Thm_mme_dwz_prescribed_z_six_finite_restriction_witness_power
import Theorems.Thm_mme_dwz_prescribed_z_power_one_class_profile_restrict
import Theorems.Thm_mme_sixSymmetrization_uniform_bigAdd_isomorphic
import Theorems.Thm_mme_finite_MM_extractions_kronFin_tau_product
import Theorems.Thm_mme_sixSymmetrization_kronFin_isomorphic
import Theorems.Thm_mme_bigAdd_mono_restrict
import Mathlib.Topology.Algebra.Order.Field

open Filter MME MME.TensorObj MME.StothersFourth
  MME.DWZRestrictedValue MME.DWZComponentRestriction MME.CompleteSplit.CWFourth
  MME.DWZQ5ExactData MME.DWZFourthGlobalWitness MME.DWZQ5AsymptoticData
  Module BigOperators
open scoped Classical Topology

universe u

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4000

/-!
# The global node of the q=5 fourth-power ledger, as a partition-node assembly

The accepted asymptotic extraction puts the 45 coarse components inside `CW_5^{⊗ 4 N t}` at
lengths `n t c = component c * D * t`, which partition the parent's `N t` fourth-power positions.
Choosing `t = L₀ * r * j` turns those into `L₀ * r * (component c * D * j)`, so each child is used
at an integer multiple of the synchronized child length and the parent at `4 * (scale * D * j)`
of it.
-/

private theorem finite_MM_copies {K : Type u} [Field K]
    (T : TensorObj K 3) (copies : ℕ) (tau lower : ℝ)
    (hextract : ∃ (k : ℕ) (a b c : Fin k → ℕ),
      TensorObj.Restrict (bigAdd (fun j ↦ MMObj K (a j) (b j) (c j))) T ∧
        lower ≤ ∑ j, (((a j * b j * c j : ℕ) : ℝ) ^ tau)) :
    ∃ (k : ℕ) (a b c : Fin k → ℕ),
      TensorObj.Restrict (bigAdd (fun j ↦ MMObj K (a j) (b j) (c j)))
        (bigAdd (fun _ : Fin copies ↦ T)) ∧
      (copies : ℝ) * lower ≤ ∑ j, (((a j * b j * c j : ℕ) : ℝ) ^ tau) := by
  obtain ⟨k, a, b, c, hres, hbound⟩ := hextract
  let index : Fin (copies * k) → Fin k := fun j ↦ (finProdFinEquiv.symm j).2
  refine ⟨copies * k, a ∘ index, b ∘ index, c ∘ index, ?_, ?_⟩
  · have hiso : Isomorphic
        (bigAdd (fun j : Fin (copies * k) ↦
          MMObj K (a (index j)) (b (index j)) (c (index j))))
        (bigAdd (fun _ : Fin copies ↦ bigAdd (fun j ↦ MMObj K (a j) (b j) (c j)))) := by
      apply TensorQ.toQ_eq_iff.mp
      simp only [TensorQ.toQ_bigAdd]
      rw [← finProdFinEquiv.sum_comp]
      simp only [index, Equiv.symm_apply_apply, Fintype.sum_prod_type,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact hiso.1.trans (mme_bigAdd_mono_restrict (fun _ ↦ hres))
  · have hsum : (∑ j : Fin (copies * k),
        (((a (index j) * b (index j) * c (index j) : ℕ) : ℝ) ^ tau)) =
        (copies : ℝ) * ∑ j, (((a j * b j * c j : ℕ) : ℝ) ^ tau) := by
      rw [← finProdFinEquiv.sum_comp]
      simp only [index, Equiv.symm_apply_apply, Fintype.sum_prod_type,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    change (copies : ℝ) * lower ≤ ∑ j : Fin (copies * k),
      (((a (index j) * b (index j) * c (index j) : ℕ) : ℝ) ^ tau)
    rw [hsum]
    exact mul_le_mul_of_nonneg_left hbound (Nat.cast_nonneg copies)

theorem solution {K : Type u} [Field K] {ιP : Type u}
    (parentBasis : Basis ιP K ((CWObj K 5).V 2))
    (parentProfile : IntegerZSplitProfile 1)
    (hden : parentProfile.denominator = 4)
    (rho : ℝ) (hrho : 0 ≤ rho) (hgap : rho < extractionRate)
    (tau : ℝ) (v : Fin 45 → ℝ) (hv : ∀ c, 0 < v c)
    (j : ℕ) (hj : 0 < j) :
    ∃ threshold : ℕ,
      PrescribedZFiniteWeightedNodeAssemblyFromLength
        (CWObj K 5)
        (fun c ↦ cwFourthConstituent K 5
          (coarseAddress c 0) (coarseAddress c 1) (coarseAddress c 2))
        parentBasis (fun _ ↦ (0 : Fin 1)) parentProfile
        (fun c ↦ constituentBasis K 5
          (coarseAddress c 0) (coarseAddress c 1) (coarseAddress c 2) 2)
        (fun c ↦ fun a : LiftedCoarseCoordinate.{u} 5 (coarseAddress c 2) ↦
          cwSquarePairGrade 5 a.down.val.1)
        (fun c ↦ rawProfile c)
        (fun c ↦ component c * D * j) (4 * (scale * D * j))
        threshold tau (Real.exp (rho / 4)) v := by
  classical
  obtain ⟨T₀, hT₀⟩ := Filter.eventually_atTop.mp
    (mme_dwz_q5_actual_standard_products_asymptotic_rate (K := K) rho hrho hgap)
  refine ⟨max T₀ 1, ?_⟩
  intro L₀ r mChild hthr hmChild hwChild
  have hLr1 : 1 ≤ L₀ * r := le_trans (le_max_right T₀ 1) hthr
  have hLrT : T₀ ≤ L₀ * r := le_trans (le_max_left T₀ 1) hthr
  have htT : T₀ ≤ L₀ * r * j :=
    hLrT.trans (Nat.le_mul_of_pos_right _ hj)
  obtain ⟨r', hcount, hrestrict⟩ := hT₀ (L₀ * r * j) htT
  -- every child denominator divides the common denominator `D`
  have hdvd : ∀ c : Fin 45, (rawProfile c).denominator ∣ D := fun c ↦
    Finset.dvd_prod_of_mem _ (Finset.mem_univ c)
  -- the child multiplicities of the extraction are integer multiples of the synchronized ones
  have hlen : ∀ c : Fin 45, (rawProfile c).denominator * mChild c = L₀ * r := hmChild
  have hmul : ∀ c : Fin 45,
      MME.DWZQ5AsymptoticData.m (L₀ * r * j) c = mChild c * (component c * D * j) := by
    intro c
    obtain ⟨D', hD'⟩ := hdvd c
    have hdpos : 0 < (rawProfile c).denominator := (rawProfile c).denominator_pos
    have hfactor : component c * (D * (L₀ * r * j))
        = (component c * D' * (L₀ * r * j)) * (rawProfile c).denominator := by
      rw [hD']; ring
    have hdiv : MME.DWZQ5AsymptoticData.m (L₀ * r * j) c
        = component c * D' * (L₀ * r * j) := by
      show component c * (D * (L₀ * r * j)) / (rawProfile c).denominator = _
      rw [hfactor, Nat.mul_div_cancel _ hdpos]
    have hgoal : (rawProfile c).denominator * (component c * D' * (L₀ * r * j))
        = (rawProfile c).denominator * (mChild c * (component c * D * j)) := by
      have := hlen c
      calc (rawProfile c).denominator * (component c * D' * (L₀ * r * j))
          = component c * D' * (rawProfile c).denominator * (L₀ * r) * j := by ring
        _ = component c * D' * (rawProfile c).denominator
              * ((rawProfile c).denominator * mChild c) * j := by rw [this]
        _ = (rawProfile c).denominator
              * (mChild c * (component c * ((rawProfile c).denominator * D') * j)) := by ring
        _ = (rawProfile c).denominator * (mChild c * (component c * D * j)) := by rw [← hD']
    rw [hdiv]
    exact Nat.eq_of_mul_eq_mul_left hdpos hgoal
  -- each child's synchronized witness is raised to the multiplicity the extraction uses
  have hwPow : ∀ c : Fin 45, SixFiniteWitness TensorObj.Restrict
      (prescribedZPower
        (cwFourthConstituent K 5 (coarseAddress c 0) (coarseAddress c 1) (coarseAddress c 2))
        (constituentBasis K 5 (coarseAddress c 0) (coarseAddress c 1) (coarseAddress c 2) 2)
        (fun a : LiftedCoarseCoordinate.{u} 5 (coarseAddress c 2) ↦
          cwSquarePairGrade 5 a.down.val.1)
        (rawProfile c) (MME.DWZQ5AsymptoticData.m (L₀ * r * j) c))
      (L₀ * r * (component c * D * j)) tau (v c) := by
    intro c
    have hbase : SixFiniteWitness TensorObj.Restrict
        (prescribedZPower
          (cwFourthConstituent K 5 (coarseAddress c 0) (coarseAddress c 1) (coarseAddress c 2))
          (constituentBasis K 5 (coarseAddress c 0) (coarseAddress c 1) (coarseAddress c 2) 2)
          (fun a : LiftedCoarseCoordinate.{u} 5 (coarseAddress c 2) ↦
            cwSquarePairGrade 5 a.down.val.1)
          (rawProfile c) (mChild c))
        ((rawProfile c).length (mChild c)) tau (v c) := by
      rw [show (rawProfile c).length (mChild c) = L₀ * r from hlen c]
      exact hwChild c
    have hpow := mme_dwz_prescribed_z_six_finite_restriction_witness_power
      (cwFourthConstituent K 5 (coarseAddress c 0) (coarseAddress c 1) (coarseAddress c 2))
      (constituentBasis K 5 (coarseAddress c 0) (coarseAddress c 1) (coarseAddress c 2) 2)
      (fun a : LiftedCoarseCoordinate.{u} 5 (coarseAddress c 2) ↦
        cwSquarePairGrade 5 a.down.val.1)
      (rawProfile c) (mChild c) (component c * D * j) tau (v c) hbase
    rw [← hmul c] at hpow
    have hlength : (rawProfile c).length
        (MME.DWZQ5AsymptoticData.m (L₀ * r * j) c) = L₀ * r * (component c * D * j) := by
      rw [hmul c]
      show (rawProfile c).denominator * (mChild c * (component c * D * j)) = _
      calc (rawProfile c).denominator * (mChild c * (component c * D * j))
          = ((rawProfile c).denominator * mChild c) * (component c * D * j) := by ring
        _ = L₀ * r * (component c * D * j) := by rw [hlen c]
    rwa [hlength] at hpow
  -- abbreviations for the extraction's child family
  set child : Fin 45 → TensorObj K 3 := fun c ↦ prescribedZPower
    (cwFourthConstituent K 5 (coarseAddress c 0) (coarseAddress c 1) (coarseAddress c 2))
    (constituentBasis K 5 (coarseAddress c 0) (coarseAddress c 1) (coarseAddress c 2) 2)
    (fun a : LiftedCoarseCoordinate.{u} 5 (coarseAddress c 2) ↦ cwSquarePairGrade 5 a.down.val.1)
    (rawProfile c) (MME.DWZQ5AsymptoticData.m (L₀ * r * j) c) with hchild
  -- one matrix extraction from the product of the children's six-symmetrizations
  obtain ⟨q, A, B, C, hMM, hweight⟩ :=
    mme_finite_MM_extractions_kronFin_tau_product
      (fun c : Fin 45 ↦ sixSymmetrization (child c)) tau
      (fun c ↦ (v c) ^ (6 * (L₀ * r * (component c * D * j))))
      (fun c ↦ pow_nonneg (hv c).le _)
      (fun c ↦ hwPow c)
  have hisoKron := mme_sixSymmetrization_kronFin_isomorphic (K := K) child
  have hMM' : TensorObj.Restrict
      (bigAdd (fun i ↦ MMObj K (A i) (B i) (C i)))
      (sixSymmetrization (kronFin 45 child)) := hMM.trans hisoKron.1
  obtain ⟨q2, A2, B2, C2, hMM2, hweight2⟩ :=
    finite_MM_copies (sixSymmetrization (kronFin 45 child)) (r' ^ 6) tau
      (∏ c : Fin 45, (v c) ^ (6 * (L₀ * r * (component c * D * j))))
      ⟨q, A, B, C, hMM', hweight⟩
  have hsix := mme_sixSymmetrization_uniform_bigAdd_isomorphic (kronFin 45 child) r'
  have hMM3 : TensorObj.Restrict
      (bigAdd (fun i ↦ MMObj K (A2 i) (B2 i) (C2 i)))
      (sixSymmetrization (bigAdd (fun _ : Fin r' ↦ kronFin 45 child))) :=
    hMM2.trans hsix.2
  -- the parent's length
  have hscale : (∑ c : Fin 45, component c) = scale :=
    mme_dwz_q5_exact_global_profile_certificate.2.2.1
  have hnc : ∀ c : Fin 45, MME.DWZQ5AsymptoticData.n (L₀ * r * j) c
      = L₀ * r * (component c * D * j) := by
    intro c
    show (rawProfile c).length (MME.DWZQ5AsymptoticData.m (L₀ * r * j) c) = _
    rw [hmul c]
    show (rawProfile c).denominator * (mChild c * (component c * D * j)) = _
    calc (rawProfile c).denominator * (mChild c * (component c * D * j))
        = ((rawProfile c).denominator * mChild c) * (component c * D * j) := by ring
      _ = L₀ * r * (component c * D * j) := by rw [hlen c]
  have hN : MME.DWZQ5AsymptoticData.N (L₀ * r * j) = L₀ * r * (scale * D * j) := by
    simp only [MME.DWZQ5AsymptoticData.N]
    rw [Finset.sum_congr rfl (fun c _ ↦ hnc c), ← Finset.mul_sum,
      ← Finset.sum_mul, ← Finset.sum_mul, hscale]
  have hL₀pos : 0 < L₀ := by
    rcases Nat.eq_zero_or_pos L₀ with h | h
    · rw [h] at hLr1; simp at hLr1
    · exact h
  have hrpos : 0 < r := by
    rcases Nat.eq_zero_or_pos r with h | h
    · rw [h] at hLr1; simp at hLr1
    · exact h
  refine ⟨MME.DWZQ5AsymptoticData.N (L₀ * r * j), r',
    (fun _ : Fin r' ↦ kronFin 45 child), q2, A2, B2, C2, ?_, ?_, ?_, ?_, hMM3, ?_⟩
  · rw [hN]
    calc r ≤ L₀ * r := Nat.le_mul_of_pos_left r hL₀pos
      _ ≤ L₀ * r * (scale * D * j) := by
          refine Nat.le_mul_of_pos_right _ ?_
          have h1 : 0 < scale := mme_dwz_q5_exact_global_profile_certificate.1
          have h2 : 0 < D := by
            refine Finset.prod_pos ?_
            intro c _
            exact (rawProfile c).denominator_pos
          exact Nat.mul_pos (Nat.mul_pos h1 h2) hj
  · simp only [IntegerZSplitProfile.length, hden, hN]
    ring
  · rw [show L₀ * r * (4 * (scale * D * j))
        = 4 * MME.DWZQ5AsymptoticData.N (L₀ * r * j) by rw [hN]; ring]
    rw [← Real.exp_nat_mul]
    have hexp : ((4 * MME.DWZQ5AsymptoticData.N (L₀ * r * j) : ℕ) : ℝ) * (rho / 4)
        = rho * (MME.DWZQ5AsymptoticData.N (L₀ * r * j) : ℝ) := by
      push_cast
      ring
    rw [hexp]
    exact hcount
  · refine hrestrict.trans ?_
    have hlenP : parentProfile.length (MME.DWZQ5AsymptoticData.N (L₀ * r * j))
        = MME.DWZQ5AsymptoticData.N (L₀ * r * j) * 4 := by
      simp only [IntegerZSplitProfile.length, hden]
      ring
    have hone := mme_dwz_prescribed_z_power_one_class_profile_restrict
      (CWObj K 5) parentBasis (fun _ ↦ (0 : Fin 1)) parentProfile
      (MME.DWZQ5AsymptoticData.N (L₀ * r * j))
    rwa [hlenP] at hone
  · refine le_trans (le_of_eq ?_) hweight2
    have hprod : (∏ c : Fin 45, (v c) ^ (component c * D * j)) ^ (6 * (L₀ * r))
        = ∏ c : Fin 45, (v c) ^ (6 * (L₀ * r * (component c * D * j))) := by
      rw [← Finset.prod_pow]
      refine Finset.prod_congr rfl fun c _ ↦ ?_
      rw [← pow_mul]
      have hexp : (component c * D * j) * (6 * (L₀ * r))
          = 6 * (L₀ * r * (component c * D * j)) := by ring
      rw [hexp]
    rw [hprod, Nat.cast_pow]
