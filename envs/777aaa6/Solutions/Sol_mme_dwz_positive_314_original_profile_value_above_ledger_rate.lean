-- Prove2me | solution 1 for mme_dwz_positive_314_original_profile_value_above_ledger_rate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-21T17:19:39.147768+00:00
-- url     : https://prove2.me/submissions/41aad751-36c5-4e0a-8cf1-731324ba12dc

import Definitions.Def_mme_dwz_profiled_regional_positions_data
import Definitions.Def_mme_recursive_profiled_CW_data
import Definitions.Def_mme_recursive_yz_cell_partition
import Definitions.Def_mme_recursive_x_hash_families
import Definitions.Def_mme_recursive_yz_owned_filters
import Theorems.Thm_mme_recursive_yz_actual_cell_product_restriction
import Theorems.Thm_mme_profiled_CW_mode_permutation_iso
import Mathlib.Algebra.BigOperators.Fin
import Theorems.Thm_mme_dwz_positive_314_integer_fine_profile_validity
import Theorems.Thm_mme_dwz_positive_314_regional_rate_identity
import Theorems.Thm_mme_dwz_positive_314_explicit_entropy_floor
import Theorems.Thm_mme_dwz_positive_314_original_profile_regional_restrict
import Theorems.Thm_mme_dwz_profiled_regional_copies_below_rate
import Theorems.Thm_mme_dwz_profiled_regional_source_restrict_perm
import Theorems.Thm_mme_bigAdd_mono_restrict
import Theorems.Thm_mme_sixSymmetrization_isomorphic_cyclic_orbit
import Theorems.Thm_mme_sixSymmetrization_isomorphic_cyclic_paired_swap
import Theorems.Thm_mme_sixSymmetrization_kronFin_isomorphic
import Theorems.Thm_mme_sixSymmetrization_restrict
import Theorems.Thm_mme_toQ_kronFin
import Definitions.Def_mme_cyclicSymmetrization_public_perm
import Definitions.Def_mme_rank_bridge
import Theorems.Thm_mme_recursive_yz_boundary_scaled_piece_eventual_witness
import Theorems.Thm_mme_canonical_square_piece_restricts_restrictedPower
import Theorems.Thm_mme_complete_split_exact_power_six_finite_witness_power
import Theorems.Thm_mme_dwz_fourth_coupled63_exact_power_six_values_explicit
import Theorems.Thm_mme_log_interval_of_exact_rational_series_certificate
import Theorems.Thm_mme_finite_MM_extractions_kronFin_tau_product

universe u

section PartNA
open BigOperators MME MME.TensorObj MME.RecursiveYZ MME.RecursiveYZ.CWCells MME.CompleteSplit
  MME.DWZProfiledRegional MME.RecursiveThinSplit
open scoped Classical


set_option autoImplicit false
set_option maxHeartbeats 400000

namespace MME.DWZMANode

/-! ## A1. The canonical positions are compatible with the canonical grouping -/

theorem size_eq {R : ℕ} (n : Fin R → ℕ) (t : ℕ) : (∑ r, t * n r) * 4 = sizeAt n t := by
  unfold sizeAt lenAt
  rw [show (2 : ℕ) ^ (2 - 1) = 2 by norm_num, ← Finset.sum_mul]
  ring

theorem positions_compat {R : ℕ} (n : Fin R → ℕ) (t : ℕ) (u : Fin (∑ r, t * n r))
    (s k : Fin 2) :
    Fin.cast (lengthAt n t) (finProdFinEquiv ((positionsAt n t).symm
        ⟨(finSigmaFinEquiv.symm u).1, (finSigmaFinEquiv.symm u).2, s⟩, k)) =
      Fin.cast (size_eq n t) (finProdFinEquiv (u, finProdFinEquiv (s, k))) := by
  apply Fin.ext
  set x := finSigmaFinEquiv.symm u with hx
  have hu : (u : ℕ) = ∑ i : Fin x.1, t * n (Fin.castLE x.1.2.le i) + x.2 := by
    rw [← finSigmaFinEquiv_apply, hx, Equiv.apply_symm_apply]
  have hpos : (((positionsAt n t).symm ⟨x.1, x.2, s⟩ : Fin (lenAt n t)) : ℕ) =
      ∑ i : Fin x.1, t * n (Fin.castLE x.1.2.le i) * 2 + (s + 2 * x.2) := by
    have e : (positionsAt n t).symm ⟨x.1, x.2, s⟩ =
        finSigmaFinEquiv ⟨x.1, finProdFinEquiv (x.2, s)⟩ := rfl
    rw [e, finSigmaFinEquiv_apply, finProdFinEquiv_apply_val]
  simp only [Fin.val_cast, finProdFinEquiv_apply_val, hpos, hu, ← Finset.sum_mul]
  ring

/-! ## A2. Cell fibres of a target address -/

theorem fiber_card {half R : ℕ} {parent : Fin R → Fin 3 → ℕ} {n : Fin R → ℕ}
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ) (a : Address half R parent n)
    (ha : a ∈ RecursiveXHash.target (n := n) m) (c : Cell half R parent) :
    Fintype.card {p : Position n // fullCell htotal a p = c} =
      m c.1 c.2 + m c.1 (complement (htotal c.1) c.2) := by
  have hjoint : ∀ r, HasJointCounts (a r) (m r) := by
    unfold RecursiveXHash.target at ha
    exact (Finset.mem_filter.mp ha).2
  obtain ⟨r0, c0⟩ := c
  have hc : ∀ x : RecursiveThinSplit.Split half (parent r0),
      (complement (htotal r0) x = c0) ↔ (x = complement (htotal r0) c0) := by
    intro x
    constructor
    · intro h; rw [← h, complement_complement]
    · intro h; rw [h, complement_complement]
  rw [Fintype.card_subtype, Finset.card_filter, Fintype.sum_sigma, Finset.sum_eq_single r0]
  · rw [Fintype.sum_prod_type]
    unfold fullCell
    simp only [Fin.sum_univ_two, Fin.isValue, ↓reduceIte, Sigma.mk.inj_iff, heq_iff_eq,
      true_and, show (1 : Fin 2) ≠ 0 by decide, hc, Finset.sum_add_distrib]
    rw [← hjoint r0 c0, ← hjoint r0 (complement (htotal r0) c0)]
    unfold RecursiveThinSplit.count
    rw [Finset.card_filter, Finset.card_filter]
  · intro r _ hr
    apply Finset.sum_eq_zero
    intro x _
    rw [if_neg]
    intro h
    exact hr (congrArg Sigma.fst h)
  · intro h; exact absurd (Finset.mem_univ r0) h

/-! ## A3. The extracted output is the product of its cell pieces -/

theorem tensor_eq_unbroken {K : Type u} [Field K] {Pt C : Type} [Fintype Pt]
    (ell L N : ℕ) (h : L * 2 ^ (ell - 1) = N) (positions : Fin L ≃ Pt)
    (cell : Pt → C) (shape : C → Fin 3 → ℕ)
    (mu : Fin 3 → C → CompleteWord ell → ℕ) :
    ProfiledCW.tensor K
        (fun i y ↦ (∀ p, grade (ProfiledCW.split positions h y p) = shape (cell p) i) ∧
          Useful cell (mu i) (ProfiledCW.split positions h y))
      = unbroken K 5 ell L positions cell shape mu := by
  subst h
  rfl

theorem output_cells {K : Type u} [Field K] {half R ell L N : ℕ}
    {parent : Fin R → Fin 3 → ℕ} {n : Fin R → ℕ}
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (a : Address half R parent n) (mu : Fin 3 → Cell half R parent → CompleteWord ell → ℕ)
    (positions : Fin L ≃ Position n) (length : L * 2 ^ (ell - 1) = N)
    (D : Partition (fullCell htotal a)) :
    TensorObj.Restrict
      (kronFin D.parts (D.piece K 5 ell (fun c i ↦ (c.2.val i).val) mu))
      (ProfiledCW.tensor K (fun i x ↦
        Graded htotal i a (ProfiledCW.split positions length x) ∧
          Useful (fullCell htotal a) (mu i) (ProfiledCW.split positions length x))) := by
  have h := tensor_eq_unbroken (K := K) ell L N length positions (fullCell htotal a)
    (fun c i ↦ (c.2.val i).val) mu
  change TensorObj.Restrict _ (ProfiledCW.tensor K (fun i y ↦
    (∀ p, grade (ProfiledCW.split positions length y p) = ((fullCell htotal a p).2.val i).val) ∧
      Useful (fullCell htotal a) (mu i) (ProfiledCW.split positions length y)))
  rw [h]
  exact mme_recursive_yz_actual_cell_product_restriction 5 ell L positions (fullCell htotal a)
    (fun c i ↦ (c.2.val i).val) mu D

/-! ## A4. Mode permutations of a single cell piece -/

theorem piece_perm_iso {K : Type u} [Field K] (N : ℕ) (s : Fin 3 → ℕ)
    (μ : Fin 3 → CompleteWord 2 → ℕ) (σ : Equiv.Perm (Fin 3))
    (hσ : σ = cyclicPerm ∨ σ = swapFirstTwoPerm) :
    Isomorphic
      (unbroken K 5 2 N (Equiv.refl _) (fun _ ↦ Unit.unit) (fun _ i ↦ s (σ.symm i))
        (fun i _ ↦ μ (σ.symm i)))
      (permObj σ (unbroken K 5 2 N (Equiv.refl _) (fun _ ↦ Unit.unit) (fun _ ↦ s)
        (fun i _ ↦ μ i))) := by
  have h := mme_profiled_CW_mode_permutation_iso (K := K) (N := N * 2 ^ (2 - 1))
    (fun i f ↦ (∀ p, grade (ProfiledCW.split (Equiv.refl (Fin N)) rfl f p) = s i) ∧
      Useful (fun _ : Fin N ↦ Unit.unit) (fun _ ↦ μ i)
        (ProfiledCW.split (Equiv.refl (Fin N)) rfl f)) σ hσ
  exact h

end MME.DWZMANode

end PartNA

section PartN314T
open BigOperators Filter MME MME.TensorObj MME.RecursiveYZ MME.RecursiveYZ.CWCells
  MME.CompleteSplit MME.DWZProfiledRegional MME.StothersFourth MME.CompleteSplit.CWFourth
  MME.DWZRestrictedValue MME.DWZComponentRestriction MME.RegionRate MME.DWZMANode
open scoped Classical


set_option autoImplicit false
set_option maxHeartbeats 400000

namespace MME.DWZMA314

open MME.DWZ314Fine

/-! ## Orientation data (the six-region frame of `DWZ314Fine`) -/

/-- `permObj (sigma c)` takes physical mode `i` from original mode `(sigma c).symm i`. -/
def sigma : Fin 6 → Equiv.Perm (Fin 3) :=
  ![Equiv.refl _, swapFirstTwoPerm, cyclicPerm.symm, cyclicPerm.symm.trans swapFirstTwoPerm,
    cyclicPerm, cyclicPerm.trans swapFirstTwoPerm]

theorem hparent : ∀ r i, parent r i = (cwFourthBlockType 3 1 4 ((sigma r).symm i)).val := by
  decide +kernel

theorem hkept : ∀ r, keptMode r = sigma r 2 := by decide +kernel

/-- The regional profile carried by each physical region. -/
abbrev prof (r : Fin 6) : IntegerZSplitProfile 5 :=
  DWZPositiveComponent314.regionalProfile (region r)

def scale (r : Fin 6) : ℕ := weightCount r * denominator

theorem prof_den (r : Fin 6) : (prof r).denominator = 1000000000000000 := by
  fin_cases r <;> rfl

theorem n_eq (r : Fin 6) : n r = (prof r).length (scale r) := by
  unfold IntegerZSplitProfile.length
  rw [prof_den]
  unfold n scale
  ring



theorem hprofile (r : Fin 6) (j : Fin 5) :
    (∑ c : {c : RecursiveThinSplit.Split 4 (parent r) // c.val (keptMode r) = j}, m r c.val) =
      (prof r).count j * scale r := by
  have h := mme_dwz_positive_314_integer_fine_profile_validity.2.2.2.2.1 r j
  rw [← Finset.sum_filter] at h
  rw [Finset.sum_subtype (p := fun c : RecursiveThinSplit.Split 4 (parent r) ↦
    c.val (keptMode r) = j) _ (fun c ↦ by simp)] at h
  rw [h]
  unfold scale
  ring

/-! ## The extraction, the cell pieces, and the rotated regional source -/

/-- The rotated regional source at extraction scale `t`. -/
noncomputable def source (K : Type u) [Field K] (t : ℕ) : TensorObj K 3 :=
  kronFin 6 (fun r ↦ permObj (sigma r)
    (prescribedZPower (cwFourthConstituent K 5 3 1 4) (constituentBasis K 5 3 1 4 2)
      (fun a : LiftedCoarseCoordinate.{u} 5 4 ↦ cwSquarePairGrade 5 a.down.val.1)
      (prof r) (t * scale r)))

/-- The cell pieces of the extracted output at address `a` and scale `t`. -/
noncomputable def pieces (K : Type u) [Field K] (t : ℕ)
    (a : Address 4 6 parent (fun r ↦ t * n r)) : TensorObj K 3 :=
  kronFin (Partition.canonical (fullCell parent_total a)).parts
    ((Partition.canonical (fullCell parent_total a)).piece K 5 2 (fun c i ↦ (c.2.val i).val)
      (fun i c w ↦ t * mu i c w))

theorem source_copies (K : Type u) [Field K] (ρ : ℝ) (hρ0 : 0 ≤ ρ)
    (hρ : ρ < regionalRate parent_total n m mu) :
    ∀ᶠ t : ℕ in atTop, ∃ k : ℕ, Real.exp (ρ * t) ≤ k ∧
      ∃ a ∈ RecursiveXHash.target (n := fun r ↦ t * n r) (fun r c ↦ t * m r c),
        TensorObj.Restrict (bigAdd (fun _ : Fin k ↦ pieces K t a)) (source K t) := by
  have hE := mme_dwz_profiled_regional_copies_below_rate (K := K) parent parent_total n
    mme_dwz_positive_314_integer_fine_profile_validity.2.2.2.2.2.2.1 (by norm_num) m mme_dwz_positive_314_integer_fine_profile_validity.1 mu mme_dwz_positive_314_integer_fine_profile_validity.2.1 mme_dwz_positive_314_integer_fine_profile_validity.2.2.1
    mme_dwz_positive_314_integer_fine_profile_validity.2.2.2.1 keptMode prof scale hprofile ρ hρ0 hρ
  filter_upwards [hE] with t ht
  obtain ⟨k, hk, a, ha, hres⟩ := ht
  refine ⟨k, hk, a, ha, ?_⟩
  have hcells := mme_bigAdd_mono_restrict (K := K) (k := k) (fun _ ↦ output_cells (K := K)
    parent_total a (fun i c w ↦ t * mu i c w) (positionsAt n t) (lengthAt n t)
    (Partition.canonical (fullCell parent_total a)))
  have hn_t : (fun r ↦ t * n r) = fun r ↦ (prof r).length (t * scale r) := by
    funext r
    rw [n_eq]
    unfold IntegerZSplitProfile.length
    ring
  have hB := mme_dwz_profiled_regional_source_restrict_perm (K := K) (fun _ ↦ 3) (fun _ ↦ 1)
    (fun _ ↦ 4) sigma prof (fun r ↦ t * scale r) parent hparent keptMode hkept
    (fun r ↦ t * n r) hn_t (positionsAt n t) (lengthAt n t) finSigmaFinEquiv.symm
    (size_eq n t) (positions_compat n t)
  exact hcells.trans (hres.trans hB)

/-! ## Orientation (copied from the accepted node-116 proof, generic in the regions) -/

theorem cyclic_kronFin_isomorphic {K : Type u} [Field K] {n : ℕ}
    (A : Fin n → TensorObj K 3) :
    Isomorphic (cyclicSymmetrization (kronFin n A))
      (kronFin n (fun r ↦ cyclicSymmetrization (A r))) := by
  apply TensorQ.toQ_eq_iff.mp
  simp only [cyclicSymmetrization_eq_public_perm, TensorQ.toQ_kron,
    mme_toQ_kronFin, ← TensorQ.permAut_toQ, map_prod, Finset.prod_mul_distrib]

theorem cyclic_square_eq_inverse : cyclicPerm.trans cyclicPerm = cyclicPerm.symm := by decide

noncomputable def regionRotation {K : Type u} [Field K]
    (A : Fin 3 → TensorObj K 3) : Fin 3 → TensorObj K 3 :=
  ![A 0, permObj cyclicPerm.symm (A 1), permObj cyclicPerm (A 2)]

noncomputable def asymmetricRegionalTensor {K : Type u} [Field K]
    (A : Fin 3 → TensorObj K 3) : TensorObj K 3 :=
  kronFin 3 (fun r ↦ kron (regionRotation A r)
    (permObj swapFirstTwoPerm (regionRotation A r)))

theorem rotated_six_isomorphic {K : Type u} [Field K]
    (A : Fin 3 → TensorObj K 3) (r : Fin 3) :
    Isomorphic (sixSymmetrization (regionRotation A r)) (sixSymmetrization (A r)) := by
  fin_cases r
  · exact Isomorphic.refl _
  · change Isomorphic (sixSymmetrization (permObj cyclicPerm.symm (A 1))) _
    rw [← cyclic_square_eq_inverse]
    exact (mme_sixSymmetrization_isomorphic_cyclic_orbit (A 1)).2
  · exact (mme_sixSymmetrization_isomorphic_cyclic_orbit (A 2)).1

theorem asymmetric_cyclic_isomorphic {K : Type u} [Field K]
    (A : Fin 3 → TensorObj K 3) :
    Isomorphic (cyclicSymmetrization (asymmetricRegionalTensor A))
      (sixSymmetrization (kronFin 3 A)) := by
  apply Isomorphic.trans (cyclic_kronFin_isomorphic _)
  apply Isomorphic.trans _ (mme_sixSymmetrization_kronFin_isomorphic A)
  apply TensorQ.toQ_eq_iff.mp
  rw [mme_toQ_kronFin, mme_toQ_kronFin]
  apply Finset.prod_congr rfl
  intro r _
  apply TensorQ.toQ_eq_iff.mpr
  exact (mme_sixSymmetrization_isomorphic_cyclic_paired_swap
    (regionRotation A r)).symm.trans (rotated_six_isomorphic A r)

theorem perm_refl_iso {K : Type u} [Field K] (T : TensorObj K 3) :
    Isomorphic (permObj (Equiv.refl _) T) T := by
  have ht : (permObj (Equiv.refl (Fin 3)) T).t = T.t := by
    change (PiTensorProduct.reindex K T.V (Equiv.refl _)) T.t = _
    rw [PiTensorProduct.reindex_refl]
    rfl
  constructor
  · refine ⟨fun _ ↦ LinearMap.id, ?_⟩
    erw [PiTensorProduct.map_id]
    exact ht.symm
  · refine ⟨fun _ ↦ LinearMap.id, ?_⟩
    erw [PiTensorProduct.map_id]
    exact ht

theorem perm_trans_iso {K : Type u} [Field K] (T : TensorObj K 3)
    (σ τ : Equiv.Perm (Fin 3)) :
    Isomorphic (permObj (σ.trans τ) T) (permObj τ (permObj σ T)) := by
  have ht : (permObj τ (permObj σ T)).t = (permObj (σ.trans τ) T).t := by
    exact PiTensorProduct.reindex_reindex σ τ T.t
  constructor
  · refine ⟨fun _ ↦ LinearMap.id, ?_⟩
    erw [PiTensorProduct.map_id]
    exact ht
  · refine ⟨fun _ ↦ LinearMap.id, ?_⟩
    erw [PiTensorProduct.map_id]
    exact ht.symm

theorem six_region_iso {K : Type u} [Field K] (A : Fin 3 → TensorObj K 3) :
    Isomorphic (kronFin 6 (fun c ↦ permObj (sigma c) (A (region c))))
      (asymmetricRegionalTensor A) := by
  apply TensorQ.toQ_eq_iff.mp
  let B := fun c : Fin 6 ↦ permObj (sigma c) (A (region c))
  let C := regionRotation A
  have h0 : TensorQ.toQ (B 0) = TensorQ.toQ (C 0) :=
    TensorQ.toQ_eq_iff.mpr (perm_refl_iso (A 0))
  have h1 : TensorQ.toQ (B 1) = TensorQ.toQ (permObj swapFirstTwoPerm (C 0)) := rfl
  have h2 : TensorQ.toQ (B 2) = TensorQ.toQ (C 1) := rfl
  have h3 : TensorQ.toQ (B 3) = TensorQ.toQ (permObj swapFirstTwoPerm (C 1)) :=
    TensorQ.toQ_eq_iff.mpr (perm_trans_iso (A 1) cyclicPerm.symm swapFirstTwoPerm)
  have h4 : TensorQ.toQ (B 4) = TensorQ.toQ (C 2) := rfl
  have h5 : TensorQ.toQ (B 5) = TensorQ.toQ (permObj swapFirstTwoPerm (C 2)) :=
    TensorQ.toQ_eq_iff.mpr (perm_trans_iso (A 2) cyclicPerm swapFirstTwoPerm)
  change TensorQ.toQ (kronFin 6 B) = TensorQ.toQ
    (kronFin 3 (fun r ↦ kron (C r) (permObj swapFirstTwoPerm (C r))))
  rw [mme_toQ_kronFin, mme_toQ_kronFin]
  simp only [TensorQ.toQ_kron, Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one]
  change TensorQ.toQ (B 0) * (TensorQ.toQ (B 1) * (TensorQ.toQ (B 2) *
    (TensorQ.toQ (B 3) * (TensorQ.toQ (B 4) * TensorQ.toQ (B 5))))) = _
  rw [h0, h1, h2, h3, h4, h5]
  change TensorQ.toQ (C 0) * (TensorQ.toQ (permObj swapFirstTwoPerm (C 0)) *
    (TensorQ.toQ (C 1) * (TensorQ.toQ (permObj swapFirstTwoPerm (C 1)) *
    (TensorQ.toQ (C 2) * TensorQ.toQ (permObj swapFirstTwoPerm (C 2)))))) =
    (TensorQ.toQ (C 0) * TensorQ.toQ (permObj swapFirstTwoPerm (C 0))) *
    ((TensorQ.toQ (C 1) * TensorQ.toQ (permObj swapFirstTwoPerm (C 1))) *
    (TensorQ.toQ (C 2) * TensorQ.toQ (permObj swapFirstTwoPerm (C 2))))
  ring

theorem kron_restrict' {K : Type u} [Field K] {X X' Y Y' : TensorObj K 3}
    (hx : TensorObj.Restrict X X') (hy : TensorObj.Restrict Y Y') :
    TensorObj.Restrict (kron X Y) (kron X' Y') := by
  obtain ⟨f, hf⟩ := hx
  obtain ⟨g, hg⟩ := hy
  refine ⟨fun i ↦ TensorProduct.map (f i) (g i), ?_⟩
  change PiTensorProduct.map (fun i ↦ TensorProduct.map (f i) (g i))
    (interchange X'.t Y'.t) = interchange X.t Y.t
  rw [TensorObj.TypeGrading.kronMap_interchange, hf, hg]

theorem cyclic_restrict {K : Type u} [Field K] {X Y : TensorObj K 3}
    (h : TensorObj.Restrict X Y) :
    TensorObj.Restrict (cyclicSymmetrization X) (cyclicSymmetrization Y) := by
  rw [cyclicSymmetrization_eq_public_perm, cyclicSymmetrization_eq_public_perm]
  exact kron_restrict' h (kron_restrict' (permObj_restrict cyclicPerm h)
    (permObj_restrict (cyclicPerm.trans cyclicPerm) h))

/-- The parent: the constituent's prescribed power at the original profile. -/
noncomputable def original (K : Type u) [Field K] (M : ℕ) : TensorObj K 3 :=
  prescribedZPower (cwFourthConstituent K 5 3 1 4) (constituentBasis K 5 3 1 4 2)
    (fun a : LiftedCoarseCoordinate.{u} 5 4 ↦ cwSquarePairGrade 5 a.down.val.1)
    DWZPositiveComponent314.parentProfile M

/-- The three regional prescribed powers at parent scale `M`. -/
noncomputable def regionA (K : Type u) [Field K] (M : ℕ) (r : Fin 3) : TensorObj K 3 :=
  prescribedZPower (cwFourthConstituent K 5 3 1 4) (constituentBasis K 5 3 1 4 2)
    (fun a : LiftedCoarseCoordinate.{u} 5 4 ↦ cwSquarePairGrade 5 a.down.val.1)
    (DWZPositiveComponent314.regionalProfile r) (DWZPositiveComponent314.regionalWeight r * M)

theorem source_eq (K : Type u) [Field K] (t : ℕ) :
    source K t = kronFin 6 (fun c ↦ permObj (sigma c) (regionA K (t * denominator) (region c))) := by
  unfold source regionA
  congr 1
  funext c
  unfold scale weightCount
  rw [show t * (DWZPositiveComponent314.regionalWeight (region c) * denominator) =
    DWZPositiveComponent314.regionalWeight (region c) * (t * denominator) by ring]

/-- Claims 7.1–7.3: the cyclically symmetrized rotated source sits inside the six-symmetrized
parent at `M = t * denominator`. -/
theorem source_parent (K : Type u) [Field K] (t : ℕ) :
    TensorObj.Restrict (cyclicSymmetrization (source K t))
      (sixSymmetrization (original K (t * denominator))) := by
  rw [source_eq]
  exact (cyclic_restrict (six_region_iso (regionA K (t * denominator))).1).trans
    ((asymmetric_cyclic_isomorphic (regionA K (t * denominator))).1.trans
      (mme_sixSymmetrization_restrict
        (mme_dwz_positive_314_original_profile_regional_restrict 5 (t * denominator)).2.2.2))

end MME.DWZMA314

end PartN314T

section PartN314C
open BigOperators Filter MME MME.TensorObj MME.RecursiveYZ MME.RecursiveYZ.CWCells
  MME.CompleteSplit MME.DWZProfiledRegional MME.StothersFourth MME.CompleteSplit.CWFourth
  MME.DWZRestrictedValue MME.DWZComponentRestriction MME.RegionRate MME.DWZMANode
open scoped Classical


set_option autoImplicit false
set_option maxHeartbeats 400000

namespace MME.DWZMA314

open MME.DWZ314Fine

/-! ## Cell pieces as a family over the cells -/

/-- Mass of a cell: its left occurrences plus its complementary right occurrences. -/
noncomputable def mass (c : Cell 4 6 parent) : ℕ :=
  m c.1 c.2 + m c.1 (complement (parent_total c.1) c.2)

/-- The cell piece at extraction scale `t`. -/
noncomputable def P (K : Type u) [Field K] (t : ℕ) (c : Cell 4 6 parent) : TensorObj K 3 :=
  unbroken K 5 2 (t * mass c) (Equiv.refl _) (fun _ ↦ Unit.unit)
    (fun _ i ↦ (c.2.val i).val) (fun i _ w ↦ t * mu i c w)

theorem unbroken_congr_N {K : Type u} [Field K] {N N' : ℕ} (h : N = N') (s : Fin 3 → ℕ)
    (μ : Fin 3 → CompleteWord 2 → ℕ) :
    unbroken K 5 2 N (Equiv.refl _) (fun _ ↦ Unit.unit) (fun _ ↦ s) (fun i _ ↦ μ i) =
      unbroken K 5 2 N' (Equiv.refl _) (fun _ ↦ Unit.unit) (fun _ ↦ s) (fun i _ ↦ μ i) := by
  subst h
  rfl

theorem piece_eq (K : Type u) [Field K] (t : ℕ) (a : Address 4 6 parent (fun r ↦ t * n r))
    (ha : a ∈ RecursiveXHash.target (n := fun r ↦ t * n r) (fun r c ↦ t * m r c))
    (j : Fin (Partition.canonical (fullCell parent_total a)).parts) :
    (Partition.canonical (fullCell parent_total a)).piece K 5 2 (fun c i ↦ (c.2.val i).val)
        (fun i c w ↦ t * mu i c w) j =
      P K t ((Partition.canonical (fullCell parent_total a)).cells j) := by
  unfold Partition.piece P
  apply unbroken_congr_N
  have hsz : (Partition.canonical (fullCell parent_total a)).size j =
      Fintype.card {p : Position (fun r ↦ t * n r) //
        fullCell parent_total a p = (Partition.canonical (fullCell parent_total a)).cells j} :=
    by dsimp only [Partition.canonical]; convert rfl
  rw [hsz, fiber_card parent_total _ a ha]
  unfold mass
  ring

theorem toQ_pieces (K : Type u) [Field K] (t : ℕ) (a : Address 4 6 parent (fun r ↦ t * n r))
    (ha : a ∈ RecursiveXHash.target (n := fun r ↦ t * n r) (fun r c ↦ t * m r c)) :
    TensorQ.toQ (pieces K t a) = ∏ c : Cell 4 6 parent, TensorQ.toQ (P K t c) := by
  unfold pieces
  rw [mme_toQ_kronFin]
  simp_rw [piece_eq K t a ha]
  exact Fintype.prod_equiv (Partition.canonical (fullCell parent_total a)).cells _ _
    (fun _ ↦ rfl)

/-! ## Splitting the cells into the six regions and pairing the XY-swapped regions -/

theorem prod_cells {M : Type*} [CommMonoid M] (g : Cell 4 6 parent → M) :
    ∏ c, g c = ∏ r : Fin 6, ∏ j : Fin 8, g ⟨r, DWZ314Fine.splitEquiv r j⟩ := by
  rw [Fintype.prod_sigma]
  exact Finset.prod_congr rfl (fun r _ ↦
    (Fintype.prod_equiv (DWZ314Fine.splitEquiv r) _ _ (fun _ ↦ rfl)).symm)

theorem splitEquiv_val (r : Fin 6) (j : Fin 8) : (DWZ314Fine.splitEquiv r j).val = DWZ314Fine.shape r j := rfl

def ev : Fin 3 → Fin 6 := ![0, 2, 4]
def od : Fin 3 → Fin 6 := ![1, 3, 5]

theorem shape_swap : ∀ (r : Fin 3) (j : Fin 8) (i : Fin 3),
    DWZ314Fine.shape (od r) j i = DWZ314Fine.shape (ev r) j (swapFirstTwoPerm.symm i) := by
  decide +kernel

theorem fine_swap : ∀ (r : Fin 3) (j : Fin 8) (i : Fin 3) (w : Fin 9),
    fineCount (od r) j i w = fineCount (ev r) j (swapFirstTwoPerm.symm i) w := by
  decide +kernel

theorem region_swap : ∀ r : Fin 3, region (od r) = region (ev r) := by decide +kernel

theorem complement_split : ∀ (r : Fin 6) (j : Fin 8),
    complement (parent_total r) (DWZ314Fine.splitMap r j) = DWZ314Fine.splitMap r (Fin.rev j) := by
  intro r j
  apply Subtype.ext
  revert r j
  decide +kernel

theorem mass_eq (r : Fin 6) (j : Fin 8) :
    mass ⟨r, DWZ314Fine.splitEquiv r j⟩ =
      weightCount r * alphaCount (region r) j * denominator +
        weightCount r * alphaCount (region r) (Fin.rev j) * denominator := by
  unfold mass m
  have h1 : (DWZ314Fine.splitEquiv r).symm (DWZ314Fine.splitEquiv r j) = j := Equiv.symm_apply_apply _ _
  have h2 : complement (parent_total r) (DWZ314Fine.splitEquiv r j) = DWZ314Fine.splitEquiv r (Fin.rev j) :=
    complement_split r j
  simp only [h1, h2, Equiv.symm_apply_apply]

theorem mu_eq (i : Fin 3) (r : Fin 6) (j : Fin 8) (w : CompleteWord 2) :
    mu i ⟨r, DWZ314Fine.splitEquiv r j⟩ w =
      weightCount r * (alphaCount (region r) j + alphaCount (region r) (Fin.rev j)) *
        fineCount r j i (wordEquiv.symm w) := by
  unfold mu
  simp only [Equiv.symm_apply_apply]

theorem pair_toQ (K : Type u) [Field K] (t : ℕ) (r : Fin 3) (j : Fin 8) :
    TensorQ.toQ (P K t ⟨od r, DWZ314Fine.splitEquiv (od r) j⟩) =
      TensorQ.permAut swapFirstTwoPerm (TensorQ.toQ (P K t ⟨ev r, DWZ314Fine.splitEquiv (ev r) j⟩)) := by
  rw [TensorQ.permAut_toQ]
  apply TensorQ.toQ_eq_iff.mpr
  have hiso := piece_perm_iso (K := K) (t * mass ⟨ev r, DWZ314Fine.splitEquiv (ev r) j⟩)
    (fun i ↦ ((DWZ314Fine.splitEquiv (ev r) j).val i).val)
    (fun i w ↦ t * mu i ⟨ev r, DWZ314Fine.splitEquiv (ev r) j⟩ w) swapFirstTwoPerm (Or.inr rfl)
  have hmass : mass ⟨od r, DWZ314Fine.splitEquiv (od r) j⟩ = mass ⟨ev r, DWZ314Fine.splitEquiv (ev r) j⟩ := by
    rw [mass_eq, mass_eq]
    unfold weightCount
    rw [region_swap]
  have hP : P K t ⟨od r, DWZ314Fine.splitEquiv (od r) j⟩ =
      unbroken K 5 2 (t * mass ⟨ev r, DWZ314Fine.splitEquiv (ev r) j⟩) (Equiv.refl _) (fun _ ↦ Unit.unit)
        (fun _ i ↦ ((DWZ314Fine.splitEquiv (ev r) j).val (swapFirstTwoPerm.symm i)).val)
        (fun i _ w ↦ t * mu (swapFirstTwoPerm.symm i) ⟨ev r, DWZ314Fine.splitEquiv (ev r) j⟩ w) := by
    unfold P
    rw [hmass]
    congr 2
    · funext _ i
      rw [splitEquiv_val, splitEquiv_val, shape_swap]
    · funext i _ w
      rw [mu_eq, mu_eq, fine_swap]
      unfold weightCount
      rw [region_swap]
  rw [hP]
  exact hiso

/-! ## The cyclic symmetrization of all pieces is the product of the six-symmetrized even pieces -/

/-- An even-region cell. -/
noncomputable def evc (r : Fin 3) (j : Fin 8) : Cell 4 6 parent :=
  ⟨ev r, DWZ314Fine.splitEquiv (ev r) j⟩

noncomputable def odc (r : Fin 3) (j : Fin 8) : Cell 4 6 parent :=
  ⟨od r, DWZ314Fine.splitEquiv (od r) j⟩

/-- The even half of the pieces. -/
noncomputable def half (K : Type u) [Field K] (t : ℕ) : TensorObj K 3 :=
  kronFin 3 (fun r ↦ kronFin 8 (fun j ↦ P K t (evc r j)))

theorem toQ_cyclic (K : Type u) [Field K] (X : TensorObj K 3) :
    TensorQ.toQ (cyclicSymmetrization X) =
      TensorQ.toQ X * (TensorQ.permAut cyclicPerm (TensorQ.toQ X) *
        TensorQ.permAut (cyclicPerm.trans cyclicPerm) (TensorQ.toQ X)) := by
  rw [cyclicSymmetrization_eq_public_perm, TensorQ.toQ_kron, TensorQ.toQ_kron,
    TensorQ.permAut_toQ, TensorQ.permAut_toQ]

theorem toQ_pieces_pair (K : Type u) [Field K] (t : ℕ) (a : Address 4 6 parent (fun r ↦ t * n r))
    (ha : a ∈ RecursiveXHash.target (n := fun r ↦ t * n r) (fun r c ↦ t * m r c)) :
    TensorQ.toQ (pieces K t a) =
      TensorQ.toQ (kron (half K t) (permObj swapFirstTwoPerm (half K t))) := by
  rw [toQ_pieces K t a ha, prod_cells, TensorQ.toQ_kron, ← TensorQ.permAut_toQ]
  unfold half
  rw [mme_toQ_kronFin, map_prod]
  simp only [mme_toQ_kronFin, map_prod]
  have hodd : ∀ r j, TensorQ.toQ (P K t ⟨od r, DWZ314Fine.splitEquiv (od r) j⟩) =
      TensorQ.permAut swapFirstTwoPerm (TensorQ.toQ (P K t (evc r j))) := pair_toQ K t
  have h6 : ∀ g : Fin 6 → TensorQ K 3, ∏ r, g r = ∏ r : Fin 3, (g (ev r) * g (od r)) := by
    intro g
    have e0 : ev 0 = 0 := rfl
    have e1 : ev 1 = 2 := rfl
    have e2 : ev 2 = 4 := rfl
    have o0 : od 0 = 1 := rfl
    have o1 : od 1 = 3 := rfl
    have o2 : od 2 = 5 := rfl
    rw [Fin.prod_univ_six, Fin.prod_univ_three, e0, e1, e2, o0, o1, o2]
    ring
  rw [h6]
  simp only [hodd, Finset.prod_mul_distrib]
  rfl

theorem cyclic_pieces_iso (K : Type u) [Field K] (t : ℕ)
    (a : Address 4 6 parent (fun r ↦ t * n r))
    (ha : a ∈ RecursiveXHash.target (n := fun r ↦ t * n r) (fun r c ↦ t * m r c)) :
    Isomorphic (cyclicSymmetrization (pieces K t a))
      (kronFin 3 (fun r ↦ kronFin 8 (fun j ↦ sixSymmetrization (P K t (evc r j))))) := by
  apply TensorQ.toQ_eq_iff.mp
  rw [toQ_cyclic, toQ_pieces_pair K t a ha, ← toQ_cyclic]
  rw [← TensorQ.toQ_eq_iff.mpr (mme_sixSymmetrization_isomorphic_cyclic_paired_swap (half K t))]
  unfold half
  rw [← TensorQ.toQ_eq_iff.mpr (mme_sixSymmetrization_kronFin_isomorphic _), mme_toQ_kronFin,
    mme_toQ_kronFin]
  apply Finset.prod_congr rfl
  intro r _
  rw [← TensorQ.toQ_eq_iff.mpr (mme_sixSymmetrization_kronFin_isomorphic _)]

end MME.DWZMA314

end PartN314C

section PartN314B
open BigOperators Filter MME MME.TensorObj MME.RecursiveYZ MME.RecursiveYZ.CWCells
  MME.CompleteSplit MME.DWZProfiledRegional MME.StothersFourth MME.CompleteSplit.CWFourth
  MME.DWZRestrictedValue MME.DWZComponentRestriction MME.RegionRate MME.DWZMANode
open scoped Classical


set_option autoImplicit false
set_option maxHeartbeats 400000

namespace MME.DWZMA314

open MME.DWZ314Fine

theorem hmass (i : Fin 3) (c : Cell 4 6 parent) : ∑ w, mu i c w = mass c :=
  mme_dwz_positive_314_integer_fine_profile_validity.2.1 i c

theorem hsupport (i : Fin 3) (c : Cell 4 6 parent) (w : CompleteWord 2) (h : 0 < mu i c w) :
    CWCells.grade w = (c.2.val i).val :=
  mme_dwz_positive_314_integer_fine_profile_validity.2.2.1 i c w h

theorem hbdry : BoundaryProfiles mu := mme_dwz_positive_314_integer_fine_profile_validity.2.2.2.1

theorem split_sum (c : Cell 4 6 parent) :
    (c.2.val 0).val + (c.2.val 1).val + (c.2.val 2).val = 4 := c.2.property.1

theorem zero_word_iff (w : CompleteWord 2) : CWCells.grade w = 0 ↔ w = fun _ ↦ 0 := by
  unfold CWCells.grade
  constructor
  · intro h
    funext r
    apply Fin.ext
    have := Finset.sum_eq_zero_iff.mp h r (Finset.mem_univ r)
    simpa using this
  · intro h
    subst h
    simp

/-- A zero-grade mode carries all its mass on the zero word. -/
theorem zero_mode (i : Fin 3) (c : Cell 4 6 parent) (hz : (c.2.val i).val = 0)
    (w : CompleteWord 2) : mu i c w = if w = (fun _ ↦ 0) then mass c else 0 := by
  have hother : ∀ w' : CompleteWord 2, w' ≠ (fun _ ↦ 0) → mu i c w' = 0 := by
    intro w' hw'
    by_contra hne
    have := hsupport i c w' (Nat.pos_of_ne_zero hne)
    rw [hz, zero_word_iff] at this
    exact hw' this
  split_ifs with hw
  · rw [← hmass i c, Finset.sum_eq_single w (fun b _ hb ↦ hother b (hw ▸ hb))
      (fun h ↦ absurd (Finset.mem_univ w) h)]
  · exact hother w hw

theorem flip_eq (w : CompleteWord 2) : Boundary.flipLabel w = fun r ↦ Fin.rev (w r) := by
  funext r
  apply Fin.ext
  simp only [Boundary.flipLabel, Fin.val_rev]
  omega

/-! ## Boundary profiles of the three zero-mode kinds -/

/-- The scaled boundary profile of a cell whose mode `z` has grade zero; `free` is the mode
carrying the profile, `idx` its grade. -/
noncomputable def bprof (c : Cell 4 6 parent) (free : Fin 3) (t : ℕ) : Boundary.Profile 2 (mass c * t) where
  index := (c.2.val free).val
  index_le := by
    have := (c.2.val free).isLt
    change (c.2.val free).val ≤ 2 * 2 ^ (2 - 1)
    omega
  count s := mu free c s * t
  total := by rw [← Finset.sum_mul, hmass]
  supported s h := by
    have hp : 0 < mu free c s := by
      rcases Nat.eq_zero_or_pos (mu free c s) with h0 | h0
      · exact absurd (by rw [h0, zero_mul]) h
      · exact h0
    exact hsupport free c s hp

/-- The unscaled boundary profile (length `mass c`). -/
noncomputable def bprof1 (c : Cell 4 6 parent) (free : Fin 3) : Boundary.Profile 2 (mass c) where
  index := (c.2.val free).val
  index_le := by
    have := (c.2.val free).isLt
    change (c.2.val free).val ≤ 2 * 2 ^ (2 - 1)
    omega
  count s := mu free c s
  total := hmass free c
  supported s h := hsupport free c s (Nat.pos_of_ne_zero h)

theorem piece_bdy (K : Type u) [Field K] (c : Cell 4 6 parent) (z free : Fin 3)
    (hzf : (z = 0 ∧ free = 1) ∨ (z = 1 ∧ free = 2) ∨ (z = 2 ∧ free = 0))
    (hz : (c.2.val z).val = 0) (t : ℕ) :
    P K t c = (bprof c free t).tensor K z := by
  unfold P Boundary.Profile.tensor
  rw [unbroken_congr_N (mul_comm t (mass c))]
  have hs := split_sum c
  rcases hzf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · congr 2
    · funext _ i
      fin_cases i <;> simp [Boundary.Profile.shape, bprof] <;> omega
    · funext i _ w
      fin_cases i
      · show t * mu 0 c w = if w = (fun _ ↦ 0) then mass c * t else 0
        rw [zero_mode 0 c hz w]
        split_ifs <;> ring
      · show t * mu 1 c w = mu 1 c w * t
        ring
      · show t * mu 2 c w = mu 1 c (Boundary.flipLabel w) * t
        rw [flip_eq, ← hbdry.2.1 c hz w]
        ring
  · congr 2
    · funext _ i
      fin_cases i <;> simp [Boundary.Profile.shape, bprof] <;> omega
    · funext i _ w
      fin_cases i
      · show t * mu 0 c w = mu 2 c (Boundary.flipLabel w) * t
        rw [flip_eq, hbdry.2.2 c hz (fun r ↦ Fin.rev (w r))]
        simp only [Fin.rev_rev]
        ring
      · show t * mu 1 c w = if w = (fun _ ↦ 0) then mass c * t else 0
        rw [zero_mode 1 c hz w]
        split_ifs <;> ring
      · show t * mu 2 c w = mu 2 c w * t
        ring
  · congr 2
    · funext _ i
      fin_cases i <;> simp [Boundary.Profile.shape, bprof] <;> omega
    · funext i _ w
      fin_cases i
      · show t * mu 0 c w = mu 0 c w * t
        ring
      · show t * mu 1 c w = mu 0 c (Boundary.flipLabel w) * t
        rw [flip_eq, ← hbdry.1 c hz w]
        ring
      · show t * mu 2 c w = if w = (fun _ ↦ 0) then mass c * t else 0
        rw [zero_mode 2 c hz w]
        split_ifs <;> ring

/-- Boundary cells: eventual witnesses below the profile's entropy rate. -/
theorem bdy_witness (K : Type u) [Field K] (c : Cell 4 6 parent) (z free : Fin 3)
    (hzf : (z = 0 ∧ free = 1) ∨ (z = 1 ∧ free = 2) ∨ (z = 2 ∧ free = 0))
    (hz : (c.2.val z).val = 0) (hL : 0 < mass c) (tau v : ℝ) (htau : 0 ≤ tau) (hv : 0 < v)
    (hvV : v < Real.exp (tau * ∑ s, Real.negMulLog ((mu free c s : ℝ) / mass c)) *
      (5 : ℝ) ^ (tau * ((∑ s, mu free c s * Boundary.ones s : ℕ) : ℝ) / mass c)) :
    ∀ᶠ t : ℕ in atTop, SixFiniteWitness TensorObj.Restrict (P K t c) (t * mass c) tau v := by
  have hG := mme_recursive_yz_boundary_scaled_piece_eventual_witness (K := K)
    (bprof1 c free) hL (bprof c free) (fun _ _ ↦ rfl) z tau v htau hv hvV
  filter_upwards [hG] with t ht
  rw [piece_bdy K c z free hzf hz t, mul_comm t (mass c)]
  exact ht

end MME.DWZMA314

end PartN314B

section PartN314I
open BigOperators Filter MME MME.TensorObj MME.RecursiveYZ MME.RecursiveYZ.CWCells
  MME.CompleteSplit MME.DWZProfiledRegional MME.StothersFourth MME.CompleteSplit.CWFourth
  MME.DWZRestrictedValue MME.DWZComponentRestriction MME.RegionRate MME.DWZMANode
open scoped Classical


set_option autoImplicit false
set_option maxHeartbeats 400000

namespace MME.DWZMA314

open MME.DWZ314Fine

/-- Witnesses move up along restrictions. -/
theorem witness_mono {K : Type u} [Field K] {A B : TensorObj K 3} {N : ℕ} {tau v : ℝ}
    (h : SixFiniteWitness TensorObj.Restrict A N tau v) (hAB : TensorObj.Restrict A B) :
    SixFiniteWitness TensorObj.Restrict B N tau v := by
  obtain ⟨k, a, b, c, h1, h2⟩ := h
  exact ⟨k, a, b, c, h1.trans (mme_sixSymmetrization_restrict hAB), h2⟩

/-- The canonical profile data of an interior cell matches a coupled row, in every orientation
the row may carry. -/
def InteriorData (c : Cell 4 6 parent) (i0 : Fin 63) : Prop :=
  Coupled63Scalar.rho i0 = c.2.val ∧
  ∀ e : Equiv.Perm (Fin 3), (e = 1 ∨ e = cyclicPerm ∨ e = cyclicPerm.trans cyclicPerm) →
    Coupled63Scalar.rho i0 = (fun a ↦ cwSquareBlockType 1 1 2 (e.symm a)) →
    ∀ k w, ((mu k c w : ℕ) : ℚ) = (mass c : ℚ) *
      CompleteSplit112.profileProbability
        (((Coupled63Scalar.rows i0).l : ℚ) /
          (2 * (((Coupled63Scalar.rows i0).l + (Coupled63Scalar.rows i0).g : ℕ) : ℚ)))
        (e.symm k) w

/-- Interior cells: witnesses at every multiple of a fixed length. -/
theorem int_witness (K : Type u) [Field K] (c : Cell 4 6 parent) (i0 : Fin 63)
    (hd : InteriorData c i0) (v : ℝ) (hv : 0 < v)
    (hvV : v < Real.exp ((Coupled63Scalar.rows i0).rate : ℝ)) :
    ∃ N0 : ℕ, 0 < N0 ∧ ∀ s : ℕ,
      SixFiniteWitness TensorObj.Restrict (P K (N0 * s) c) (N0 * s * mass c)
        (790643 / 1000000 : ℝ) v := by
  obtain ⟨e, he, hrho, beta, hbeta, hrate⟩ :=
    mme_dwz_fourth_coupled63_exact_power_six_values_explicit K i0
  obtain ⟨m0, hm0, hlen, hw⟩ := hrate.2 v hv hvV 1
  set N0 := 2 * (((Coupled63Scalar.rows i0).l + (Coupled63Scalar.rows i0).g) * m0) with hN0
  refine ⟨N0, lt_of_lt_of_le Nat.zero_lt_one hlen, fun s ↦ ?_⟩
  have hpow := mme_complete_split_exact_power_six_finite_witness_power
    (CompleteSplitCanonicalSquare.obj K 5 (Coupled63Scalar.rho i0))
    (CompleteSplitCanonicalSquare.basis K 5 (Coupled63Scalar.rho i0))
    (CompleteSplitCanonicalSquare.label 5 (Coupled63Scalar.rho i0)) beta N0 (s * mass c)
    (790643 / 1000000 : ℝ) v hw
  have hD := mme_canonical_square_piece_restricts_restrictedPower (K := K)
    (Coupled63Scalar.rho i0) (N0 * (s * mass c)) beta (fun k w ↦ N0 * s * mu k c w) (by
      intro k w
      rw [hbeta k w]
      have h := hd.2 e he hrho k w
      have h' : ((mu k c w : ℕ) : ℝ) = (mass c : ℝ) *
          ((CompleteSplit112.profileProbability
            (((Coupled63Scalar.rows i0).l : ℚ) /
              (2 * (((Coupled63Scalar.rows i0).l + (Coupled63Scalar.rows i0).g : ℕ) : ℚ)))
            (e.symm k) w : ℚ) : ℝ) := by exact_mod_cast h
      simp only [Nat.cast_mul]
      rw [h']
      ring)
  have hP : P K (N0 * s) c = RecursiveYZ.CWCells.unbroken K 5 2 (N0 * (s * mass c))
      (Equiv.refl _) (fun _ ↦ Unit.unit) (fun _ i ↦ (Coupled63Scalar.rho i0 i).val)
      (fun k _ w ↦ N0 * s * mu k c w) := by
    unfold P
    rw [unbroken_congr_N (show N0 * s * mass c = N0 * (s * mass c) by ring)]
    rw [hd.1]
  rw [hP, show N0 * s * mass c = N0 * (s * mass c) by ring]
  exact witness_mono hpow hD

end MME.DWZMA314

end PartN314I

section PartN314R
open BigOperators Filter MME MME.TensorObj MME.RecursiveYZ MME.RecursiveYZ.CWCells
  MME.CompleteSplit MME.DWZProfiledRegional MME.StothersFourth MME.CompleteSplit.CWFourth
  MME.DWZRestrictedValue MME.DWZComponentRestriction MME.RegionRate MME.DWZMANode
open scoped Classical


set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

namespace MME.DWZMA314

open MME.DWZ314Fine

/-! ## Certified logarithms (the accepted coupled-row machinery) -/

def lscale (q : ℚ) : ℕ :=
  ((List.range 20).find? fun k => 1 ≤ q * 2 ^ k).getD 0

def logParameter (q : ℚ) (k : ℕ) : ℚ :=
  (q * 2 ^ k - 1) / (q * 2 ^ k + 1)

def logPartial (q : ℚ) (k : ℕ) : ℚ :=
  ∑ j ∈ Finset.range 10, logParameter q k ^ (2 * j + 1) / (2 * j + 1)

def logLower (q : ℚ) (k : ℕ) : ℚ :=
  2 * logPartial q k - k * (69314718057 / 100000000000 : ℚ)

def logUpper (q : ℚ) (k : ℕ) : ℚ :=
  2 * (logPartial q k + logParameter q k ^ 21 /
    (1 - logParameter q k ^ 2)) - k * (69314718055 / 100000000000 : ℚ)

theorem logInterval (q : ℚ) (k : ℕ) (hq : 0 < q) (hscale : 1 ≤ q * 2 ^ k) :
    (logLower q k : ℝ) ≤ Real.log (q : ℝ) ∧ Real.log (q : ℝ) ≤ (logUpper q k : ℝ) := by
  let x : ℚ := q * 2 ^ k
  have hx : 0 < x := lt_of_lt_of_le (by norm_num) hscale
  have hxp : 0 < x + 1 := by linarith
  apply mme_log_interval_of_exact_rational_series_certificate
    q (logParameter q k) (logLower q k) (logUpper q k) k 10 hq
  · exact div_nonneg (sub_nonneg.mpr hscale) hxp.le
  · change (x - 1) / (x + 1) < 1
    rw [div_lt_one hxp]
    linarith
  · dsimp [logParameter, x]
    field_simp
    ring
  · simp [logLower, logPartial]
  · simp [logUpper, logPartial]

def log5Lower : ℚ := logLower (5 / 4) 0 + 2 * logLower 2 0

theorem log5Lower_le : (log5Lower : ℝ) ≤ Real.log 5 := by
  have h5 := (logInterval (5 / 4) 0 (by norm_num) (by norm_num)).1
  have h2 := (logInterval 2 0 (by norm_num) (by norm_num)).1
  have heq : Real.log (5 : ℝ) =
      Real.log ((5 / 4 : ℚ) : ℝ) + 2 * Real.log 2 := by
    rw [show (5 : ℝ) = (((5 / 4 : ℚ) : ℝ) * 2 ^ 2) by norm_num,
      Real.log_mul (by norm_num : (((5 / 4 : ℚ) : ℝ) ≠ 0))
        (by norm_num : (2 : ℝ) ^ 2 ≠ 0), Real.log_pow]
    norm_num
  rw [heq]
  simpa [log5Lower] using add_le_add h5
    (mul_le_mul_of_nonneg_left h2 (by norm_num : (0 : ℝ) ≤ 2))

/-! ## Profile entropies -/

/-- Probability of word `w` in profile `k`. -/
def pk (k : Fin 12) (w : Fin 9) : ℚ := (profileCount k w : ℚ) / denominator

def entropyLowerK (k : Fin 12) : ℚ :=
  ∑ w : Fin 9, if profileCount k w = 0 then 0 else -(pk k w * logUpper (pk k w) (lscale (pk k w)))

def onesW : Fin 9 → ℕ := ![0, 1, 0, 1, 2, 1, 0, 1, 0]

def onesK (k : Fin 12) : ℚ := ∑ w : Fin 9, pk k w * onesW w

def tauQ : ℚ := 790643 / 1000000

def rateLowK (k : Fin 12) : ℚ := tauQ * (entropyLowerK k + onesK k * log5Lower)

theorem pk_cert : ∀ (k : Fin 12) (w : Fin 9), profileCount k w ≠ 0 →
    0 < pk k w ∧ 1 ≤ pk k w * 2 ^ lscale (pk k w) := by
  decide +kernel

theorem entropyLowerK_le (k : Fin 12) :
    (entropyLowerK k : ℝ) ≤ ∑ w : Fin 9, Real.negMulLog (pk k w : ℝ) := by
  unfold entropyLowerK
  push_cast
  apply Finset.sum_le_sum
  intro w _
  split_ifs with h
  · simp [pk, h]
  · obtain ⟨hpos, hsc⟩ := pk_cert k w h
    have hlog := (logInterval (pk k w) (lscale (pk k w)) hpos hsc).2
    have hp : (0 : ℝ) < (pk k w : ℝ) := by exact_mod_cast hpos
    simp only [Rat.cast_neg, Rat.cast_mul, Real.negMulLog]
    nlinarith [mul_le_mul_of_nonneg_left hlog hp.le]

theorem ones_word : ∀ w : Fin 9, Boundary.ones (word w) = onesW w := by
  decide +kernel

theorem onesK_nonneg (k : Fin 12) : 0 ≤ onesK k := by
  unfold onesK pk
  apply Finset.sum_nonneg
  intro w _
  positivity

/-! ## The entropy rate of a boundary cell -/

theorem wordEquiv_apply (w : Fin 9) : wordEquiv w = word w := rfl

theorem ratio (r6 : Fin 6) (j : Fin 8) (i : Fin 3) (s : CompleteWord 2)
    (hpos : 0 < weightCount r6 * (alphaCount (region r6) j + alphaCount (region r6) (Fin.rev j))) :
    (mu i ⟨r6, DWZ314Fine.splitEquiv r6 j⟩ s : ℝ) / (mass ⟨r6, DWZ314Fine.splitEquiv r6 j⟩ : ℝ) =
      (pk (profileIndex r6 j i) (wordEquiv.symm s) : ℝ) := by
  rw [mu_eq, mass_eq]
  have hd : (0 : ℝ) < denominator := by unfold denominator; norm_num
  have hw : (0 : ℝ) < (weightCount r6 : ℝ) *
      ((alphaCount (region r6) j : ℝ) + (alphaCount (region r6) (Fin.rev j) : ℝ)) := by
    exact_mod_cast hpos
  unfold pk fineCount
  push_cast
  rw [div_eq_div_iff (ne_of_gt (by nlinarith [mul_pos hw hd])) hd.ne']
  ring

/-- The rate a boundary cell offers dominates the certified profile rate. -/
theorem cell_rate (r6 : Fin 6) (j : Fin 8) (free : Fin 3)
    (hpos : 0 < weightCount r6 * (alphaCount (region r6) j + alphaCount (region r6) (Fin.rev j)))
    (eps : ℚ) (heps : 0 < eps) :
    Real.exp ((rateLowK (profileIndex r6 j free) - eps : ℚ) : ℝ) <
      Real.exp ((790643 / 1000000 : ℝ) * ∑ s, Real.negMulLog
          ((mu free ⟨r6, DWZ314Fine.splitEquiv r6 j⟩ s : ℝ) /
            mass ⟨r6, DWZ314Fine.splitEquiv r6 j⟩)) *
        (5 : ℝ) ^ ((790643 / 1000000 : ℝ) *
          ((∑ s, mu free ⟨r6, DWZ314Fine.splitEquiv r6 j⟩ s * Boundary.ones s : ℕ) : ℝ) /
            mass ⟨r6, DWZ314Fine.splitEquiv r6 j⟩) := by
  have hr : ∀ s, (mu free ⟨r6, DWZ314Fine.splitEquiv r6 j⟩ s : ℝ) /
      (mass ⟨r6, DWZ314Fine.splitEquiv r6 j⟩ : ℝ) =
      (pk (profileIndex r6 j free) (wordEquiv.symm s) : ℝ) := fun s ↦ ratio r6 j free s hpos
  have hH : ∑ s, Real.negMulLog ((mu free ⟨r6, DWZ314Fine.splitEquiv r6 j⟩ s : ℝ) /
      mass ⟨r6, DWZ314Fine.splitEquiv r6 j⟩) =
      ∑ w : Fin 9, Real.negMulLog (pk (profileIndex r6 j free) w : ℝ) := by
    simp_rw [hr]
    exact Fintype.sum_equiv wordEquiv.symm _ _ (fun _ ↦ rfl)
  have hE : ((∑ s, mu free ⟨r6, DWZ314Fine.splitEquiv r6 j⟩ s * Boundary.ones s : ℕ) : ℝ) /
      mass ⟨r6, DWZ314Fine.splitEquiv r6 j⟩ = (onesK (profileIndex r6 j free) : ℝ) := by
    push_cast
    rw [Finset.sum_div]
    have h1 : ∀ s, (mu free ⟨r6, DWZ314Fine.splitEquiv r6 j⟩ s : ℝ) * (Boundary.ones s : ℝ) /
        mass ⟨r6, DWZ314Fine.splitEquiv r6 j⟩ =
        (pk (profileIndex r6 j free) (wordEquiv.symm s) : ℝ) * (Boundary.ones s : ℝ) := by
      intro s
      rw [mul_div_right_comm, hr s]
    simp_rw [h1]
    unfold onesK
    push_cast
    refine Fintype.sum_equiv wordEquiv.symm _ _ (fun s ↦ ?_)
    congr 1
    have hs : Boundary.ones s = onesW (wordEquiv.symm s) := by
      rw [← ones_word, ← wordEquiv_apply, Equiv.apply_symm_apply]
    rw [hs]
  set k := profileIndex r6 j free
  rw [hH, mul_div_assoc, hE]
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 5), ← Real.exp_add]
  apply Real.exp_lt_exp.mpr
  have h1 := entropyLowerK_le k
  have h2 := log5Lower_le
  have hO : (0 : ℝ) ≤ onesK k := by exact_mod_cast onesK_nonneg k
  have hepsR : (0 : ℝ) < eps := by exact_mod_cast heps
  unfold rateLowK tauQ
  push_cast
  nlinarith [mul_le_mul_of_nonneg_left h2 hO]

end MME.DWZMA314

end PartN314R

section PartN314F
open BigOperators Filter MME MME.TensorObj MME.RecursiveYZ MME.RecursiveYZ.CWCells
  MME.CompleteSplit MME.DWZProfiledRegional MME.StothersFourth MME.CompleteSplit.CWFourth
  MME.DWZRestrictedValue MME.DWZComponentRestriction MME.RegionRate MME.DWZMANode
open scoped Classical


set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

namespace MME.DWZMA314

open MME.DWZ314Fine

/-! ## Cell tables (even regions `ev r`, splits `j`) -/

def isInt : Fin 3 → Fin 8 → Bool :=
  ![![false, false, false, true, false, true, false, false], ![false, false, false, true, false, true, false, false], ![false, false, false, true, false, true, false, false]]

def zB : Fin 3 → Fin 8 → Fin 3 :=
  ![![0, 0, 1, 0, 1, 0, 1, 2], ![0, 2, 0, 0, 0, 0, 0, 1], ![1, 1, 2, 0, 2, 0, 2, 0]]

def fB : Fin 3 → Fin 8 → Fin 3 :=
  ![![1, 1, 2, 0, 2, 0, 2, 0], ![1, 0, 1, 0, 1, 0, 1, 2], ![2, 2, 0, 0, 0, 0, 0, 1]]

def rowI : Fin 3 → Fin 8 → Fin 63 :=
  ![![0, 0, 0, 33, 0, 2, 0, 0], ![0, 0, 0, 1, 0, 33, 0, 0], ![0, 0, 0, 2, 0, 1, 0, 0]]

def epsQ : ℚ := 1 / 1000000000000000

/-- The certified per-position log-rate of each even cell. -/
def rq (r : Fin 3) (j : Fin 8) : ℚ :=
  if isInt r j then (Coupled63Scalar.rows (rowI r j)).rate - epsQ
  else rateLowK (profileIndex (ev r) j (fB r j)) - epsQ

theorem bdy_table : ∀ (r : Fin 3) (j : Fin 8), isInt r j = false →
    ((zB r j = 0 ∧ fB r j = 1) ∨ (zB r j = 1 ∧ fB r j = 2) ∨ (zB r j = 2 ∧ fB r j = 0)) ∧
      (DWZ314Fine.shape (ev r) j (zB r j)).val = 0 := by
  decide +kernel

theorem pos_table : ∀ (r : Fin 3) (j : Fin 8),
    0 < weightCount (ev r) *
      (alphaCount (region (ev r)) j + alphaCount (region (ev r)) (Fin.rev j)) := by
  decide +kernel

theorem mass_pos (r : Fin 3) (j : Fin 8) : 0 < mass (evc r j) := by
  unfold evc
  rw [mass_eq]
  have h := pos_table r j
  have hd : 0 < denominator := by unfold denominator; norm_num
  nlinarith [Nat.mul_le_mul_right denominator (Nat.succ_le_of_lt h)]

/-! ## Interior cells match their coupled rows -/

def ePerm : Fin 3 → Equiv.Perm (Fin 3) := ![1, cyclicPerm, cyclicPerm.trans cyclicPerm]

theorem int_rho : ∀ (r : Fin 3) (j : Fin 8), isInt r j = true →
    Coupled63Scalar.rho (rowI r j) = DWZ314Fine.shape (ev r) j := by
  decide +kernel

/-- The rational identity behind `InteriorData`, over the explicit orientations. -/
theorem int_identity : ∀ (r : Fin 3) (j : Fin 8), isInt r j = true → ∀ q : Fin 3,
    Coupled63Scalar.rho (rowI r j) = (fun a ↦ cwSquareBlockType 1 1 2 ((ePerm q).symm a)) →
    ∀ (k : Fin 3) (w : Fin 9),
      ((weightCount (ev r) * (alphaCount (region (ev r)) j +
          alphaCount (region (ev r)) (Fin.rev j)) * fineCount (ev r) j k w : ℕ) : ℚ) =
        ((weightCount (ev r) * alphaCount (region (ev r)) j * denominator +
          weightCount (ev r) * alphaCount (region (ev r)) (Fin.rev j) * denominator : ℕ) : ℚ) *
        CompleteSplit112.profileProbability
          (((Coupled63Scalar.rows (rowI r j)).l : ℚ) /
            (2 * (((Coupled63Scalar.rows (rowI r j)).l +
              (Coupled63Scalar.rows (rowI r j)).g : ℕ) : ℚ)))
          ((ePerm q).symm k) (word w) := by
  decide +kernel

theorem int_data (r : Fin 3) (j : Fin 8) (h : isInt r j = true) :
    InteriorData (evc r j) (rowI r j) := by
  refine ⟨int_rho r j h, ?_⟩
  intro e he hrho k w
  obtain ⟨w', rfl⟩ := wordEquiv.surjective w
  have hq : ∃ q : Fin 3, e = ePerm q := by
    rcases he with rfl | rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
  obtain ⟨q, rfl⟩ := hq
  unfold evc
  rw [mu_eq, mass_eq, Equiv.symm_apply_apply, wordEquiv_apply]
  exact int_identity r j h q hrho k w'

/-! ## Uniform cell witnesses -/

theorem cell_witness (K : Type u) [Field K] (r : Fin 3) (j : Fin 8) :
    ∃ N0 : ℕ, 0 < N0 ∧ ∀ᶠ s : ℕ in atTop,
      SixFiniteWitness TensorObj.Restrict (P K (N0 * s) (evc r j)) (N0 * s * mass (evc r j))
        (790643 / 1000000 : ℝ) (Real.exp (rq r j : ℝ)) := by
  cases h : isInt r j
  · obtain ⟨hzf, hz⟩ := bdy_table r j h
    have hvV := cell_rate (ev r) j (fB r j) (pos_table r j) epsQ (by unfold epsQ; norm_num)
    have hrq : rq r j = rateLowK (profileIndex (ev r) j (fB r j)) - epsQ := by
      unfold rq; simp [h]
    rw [← hrq] at hvV
    have hW := bdy_witness K (evc r j) (zB r j) (fB r j) hzf hz (mass_pos r j)
      (790643 / 1000000 : ℝ) (Real.exp (rq r j : ℝ)) (by norm_num) (Real.exp_pos _) hvV
    refine ⟨1, Nat.one_pos, ?_⟩
    filter_upwards [hW] with s hs
    simpa only [one_mul] using hs
  · have hrq : rq r j = (Coupled63Scalar.rows (rowI r j)).rate - epsQ := by
      unfold rq; simp [h]
    obtain ⟨N0, hN0, hall⟩ := int_witness K (evc r j) (rowI r j) (int_data r j h)
      (Real.exp (rq r j : ℝ)) (Real.exp_pos _) (by
        rw [hrq]
        apply Real.exp_lt_exp.mpr
        push_cast
        have : (0 : ℝ) < (epsQ : ℝ) := by unfold epsQ; norm_num
        linarith)
    exact ⟨N0, hN0, Eventually.of_forall hall⟩

/-! ## The floor certificate -/

def Fq : ℚ := 1539739919103 / 250000000000

def rho0 : ℚ := 1369594511 / 2000000000

theorem floor_cert : (1000000000000001000000000000000 : ℚ) * Fq ≤
    1000000000000001000000000000000 * rho0 + ∑ r : Fin 3, ∑ j : Fin 8,
      ((weightCount (ev r) * (alphaCount (region (ev r)) j +
        alphaCount (region (ev r)) (Fin.rev j)) : ℕ) : ℚ) * rq r j := by
  decide +kernel

/-! ## Copies and the parent (copied from the accepted node-116 proof) -/

theorem cyclic_copies_isomorphic {K : Type u} [Field K] (T : TensorObj K 3) (k : ℕ) :
    Isomorphic (cyclicSymmetrization (bigAdd (fun _ : Fin k ↦ T)))
      (bigAdd (fun _ : Fin (k ^ 3) ↦ cyclicSymmetrization T)) := by
  apply TensorQ.toQ_eq_iff.mp
  simp only [cyclicSymmetrization_eq_public_perm, TensorQ.toQ_bigAdd,
    TensorQ.toQ_kron, ← TensorQ.permAut_toQ,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_pow, map_mul, map_natCast]
  ring

theorem finite_MM_copies {K : Type u} [Field K] (T : TensorObj K 3) (copies : ℕ) (tau lower : ℝ)
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

theorem finite_parent_of_cyclic_copies {K : Type u} [Field K]
    (A B Q : TensorObj K 3) (copies : ℕ) (tau lower : ℝ)
    (hcopy : TensorObj.Restrict (bigAdd (fun _ : Fin copies ↦ B)) Q)
    (hparent : TensorObj.Restrict (cyclicSymmetrization Q) (sixSymmetrization A))
    (hchild : ∃ (k : ℕ) (a b c : Fin k → ℕ),
      TensorObj.Restrict (bigAdd (fun j ↦ MMObj K (a j) (b j) (c j)))
        (cyclicSymmetrization B) ∧
      lower ≤ ∑ j, (((a j * b j * c j : ℕ) : ℝ) ^ tau)) :
    ∃ (k : ℕ) (a b c : Fin k → ℕ),
      TensorObj.Restrict (bigAdd (fun j ↦ MMObj K (a j) (b j) (c j)))
        (sixSymmetrization A) ∧
      ((copies ^ 3 : ℕ) : ℝ) * lower ≤
        ∑ j, (((a j * b j * c j : ℕ) : ℝ) ^ tau) := by
  obtain ⟨k, a, b, c, hres, hbound⟩ :=
    finite_MM_copies (cyclicSymmetrization B) (copies ^ 3) tau lower hchild
  exact ⟨k, a, b, c,
    hres.trans ((cyclic_copies_isomorphic B copies).2.trans
      ((cyclic_restrict hcopy).trans hparent)), hbound⟩

/-! ## The value transfer -/

theorem product_exp_pow {ι : Type*} [Fintype ι] (a : ι → ℝ) (m : ι → ℕ) :
    (∏ i, (Real.exp (a i)) ^ (m i)) = Real.exp (∑ i, (m i : ℝ) * a i) := by
  simp only [← Real.exp_nat_mul]
  exact (Real.exp_sum _ _).symm

theorem mass_real (r : Fin 3) (j : Fin 8) :
    (mass (evc r j) : ℝ) = ((weightCount (ev r) * (alphaCount (region (ev r)) j +
        alphaCount (region (ev r)) (Fin.rev j)) : ℕ) : ℝ) * denominator := by
  unfold evc
  rw [mass_eq]
  push_cast
  ring

theorem parent_len (M : ℕ) :
    DWZPositiveComponent314.parentProfile.length M = 1000000000000001000000000000000 * M := rfl

/-- The numerical heart: copies times children dominate the parent base. -/
theorem value_bound (t k : ℕ) (hk : Real.exp ((rho0 : ℝ) * totalCount * t) ≤ k) :
    (Real.exp (Fq : ℝ)) ^ (6 * DWZPositiveComponent314.parentProfile.length (t * denominator)) ≤
      ((k ^ 3 : ℕ) : ℝ) * ∏ r : Fin 3, ∏ j : Fin 8,
        (Real.exp (rq r j : ℝ)) ^ (6 * (t * mass (evc r j))) := by
  have hprod : (∏ r : Fin 3, ∏ j : Fin 8, (Real.exp (rq r j : ℝ)) ^ (6 * (t * mass (evc r j)))) =
      Real.exp (∑ r : Fin 3, ∑ j : Fin 8, ((6 * (t * mass (evc r j)) : ℕ) : ℝ) * (rq r j : ℝ)) := by
    rw [Real.exp_sum]
    apply Finset.prod_congr rfl
    intro r _
    exact product_exp_pow _ _
  have hk3 : Real.exp (3 * ((rho0 : ℝ) * totalCount * t)) ≤ ((k ^ 3 : ℕ) : ℝ) := by
    have h := pow_le_pow_left₀ (Real.exp_pos _).le hk 3
    rw [← Real.exp_nat_mul] at h
    push_cast
    simpa using h
  rw [hprod, parent_len, ← Real.exp_nat_mul]
  calc Real.exp (((6 * (1000000000000001000000000000000 * (t * denominator)) : ℕ) : ℝ) * (Fq : ℝ))
      ≤ Real.exp (3 * ((rho0 : ℝ) * totalCount * t) +
          ∑ r : Fin 3, ∑ j : Fin 8, ((6 * (t * mass (evc r j)) : ℕ) : ℝ) * (rq r j : ℝ)) := by
        apply Real.exp_le_exp.mpr
        set S : ℝ := ∑ r : Fin 3, ∑ j : Fin 8, (weightCount (ev r) : ℝ) *
          ((alphaCount (region (ev r)) j : ℝ) + (alphaCount (region (ev r)) (Fin.rev j) : ℝ)) *
            (rq r j : ℝ) with hS
        have hf : (1000000000000001000000000000000 : ℝ) * (Fq : ℝ) ≤
            1000000000000001000000000000000 * (rho0 : ℝ) + S := by
          have h := floor_cert
          have h' : ((1000000000000001000000000000000 * Fq : ℚ) : ℝ) ≤
              ((1000000000000001000000000000000 * rho0 + ∑ r : Fin 3, ∑ j : Fin 8,
                ((weightCount (ev r) * (alphaCount (region (ev r)) j +
                  alphaCount (region (ev r)) (Fin.rev j)) : ℕ) : ℚ) * rq r j : ℚ) : ℝ) := by
            exact_mod_cast h
          rw [hS]
          push_cast at h'
          exact h'
        have hsum : (∑ r : Fin 3, ∑ j : Fin 8, ((6 * (t * mass (evc r j)) : ℕ) : ℝ) * (rq r j : ℝ)) =
            6 * t * denominator * S := by
          rw [hS, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro r _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          have hm := mass_real r j
          push_cast at hm ⊢
          rw [hm]
          ring
        rw [hsum]
        have htot : (totalCount : ℝ) = 2000000000000002000000000000000 * denominator := by
          unfold totalCount
          push_cast
          ring
        rw [htot]
        have hpos : (0 : ℝ) ≤ 6 * t * denominator :=
          mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
        have key := mul_le_mul_of_nonneg_left hf hpos
        have hcast : (((6 * (1000000000000001000000000000000 * (t * denominator))) : ℕ) : ℝ) =
            6 * (1000000000000001000000000000000 * ((t : ℝ) * denominator)) := by
          push_cast; ring
        rw [hcast]
        nlinarith [key]
    _ = Real.exp (3 * ((rho0 : ℝ) * totalCount * t)) *
          Real.exp (∑ r : Fin 3, ∑ j : Fin 8, ((6 * (t * mass (evc r j)) : ℕ) : ℝ) * (rq r j : ℝ)) :=
        Real.exp_add _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right hk3 (Real.exp_pos _).le

/-- **Node 134** (ledger object 151): the constituent `T_{1,3,4}` of `CW_5^{⊗4}`, at its original
parent profile, has prescribed-Z six value at least `exp(769869971361/125000000000)`. -/
theorem value314 {K : Type u} [Field K] :
    HasPrescribedZSixRestrictionValueAtLeast (cwFourthConstituent K 5 3 1 4)
      (constituentBasis K 5 3 1 4 2)
      (fun a : LiftedCoarseCoordinate.{u} 5 4 ↦ cwSquarePairGrade 5 a.down.val.1)
      DWZPositiveComponent314.parentProfile (790643 / 1000000) (Real.exp (Fq : ℝ)) := by
  refine ⟨(Real.exp_pos _).le, ?_⟩
  intro v hv hvF cutoff
  have htc : (0 : ℝ) < totalCount := by unfold totalCount denominator; norm_num
  have hρ : (rho0 : ℝ) * totalCount < regionalRate parent_total n m mu := by
    rw [mme_dwz_positive_314_regional_rate_identity]
    have hf := mme_dwz_positive_314_explicit_entropy_floor
    have h0 : (rho0 : ℝ) = 1369594511 / 2000000000 := by unfold rho0; push_cast; ring
    rw [h0, mul_comm]
    exact mul_lt_mul_of_pos_left hf htc
  have hT := source_copies K ((rho0 : ℝ) * totalCount) (by unfold rho0; positivity) hρ
  choose N0 hN0 hW using fun rj : Fin 3 × Fin 8 ↦ cell_witness K rj.1 rj.2
  have hcell : ∀ rj : Fin 3 × Fin 8, ∀ᶠ s : ℕ in atTop,
      SixFiniteWitness TensorObj.Restrict (P K ((∏ x, N0 x) * s) (evc rj.1 rj.2))
        ((∏ x, N0 x) * s * mass (evc rj.1 rj.2)) (790643 / 1000000 : ℝ)
        (Real.exp (rq rj.1 rj.2 : ℝ)) := by
    intro rj
    have hsplit : (∏ x, N0 x) = N0 rj * ∏ x ∈ Finset.univ.erase rj, N0 x :=
      (Finset.mul_prod_erase _ _ (Finset.mem_univ rj)).symm
    have hMpos : 0 < ∏ x ∈ Finset.univ.erase rj, N0 x := Finset.prod_pos (fun x _ ↦ hN0 x)
    have htend : Tendsto (fun s : ℕ ↦ (∏ x ∈ Finset.univ.erase rj, N0 x) * s) atTop atTop :=
      Filter.tendsto_atTop_mono (fun s ↦ Nat.le_mul_of_pos_left s hMpos) tendsto_id
    filter_upwards [htend.eventually (hW rj)] with s hs
    rw [hsplit, mul_assoc]
    exact hs
  have hall := Filter.eventually_all.mpr hcell
  have hLpos : 0 < ∏ x, N0 x := Finset.prod_pos (fun x _ ↦ hN0 x)
  have htendL : Tendsto (fun s : ℕ ↦ (∏ x, N0 x) * s) atTop atTop :=
    Filter.tendsto_atTop_mono (fun s ↦ Nat.le_mul_of_pos_left s hLpos) tendsto_id
  obtain ⟨s, hs1, hs2, hs3⟩ :=
    (hall.and ((htendL.eventually hT).and (eventually_ge_atTop (cutoff + 1)))).exists
  set t := (∏ x, N0 x) * s with ht
  obtain ⟨k, hk, a, ha, hres⟩ := hs2
  have hext : ∀ r : Fin 3, ∃ (q : ℕ) (A B C : Fin q → ℕ),
      TensorObj.Restrict (bigAdd (fun i ↦ MMObj K (A i) (B i) (C i)))
        (kronFin 8 (fun j ↦ sixSymmetrization (P K t (evc r j)))) ∧
      (∏ j : Fin 8, (Real.exp (rq r j : ℝ)) ^ (6 * (t * mass (evc r j)))) ≤
        ∑ i, (((A i * B i * C i : ℕ) : ℝ) ^ (790643 / 1000000 : ℝ)) := by
    intro r
    apply mme_finite_MM_extractions_kronFin_tau_product
      (fun j ↦ sixSymmetrization (P K t (evc r j))) (790643 / 1000000 : ℝ)
      (fun j ↦ (Real.exp (rq r j : ℝ)) ^ (6 * (t * mass (evc r j)))) (fun j ↦ by positivity)
    intro j
    obtain ⟨q, A, B, C, hr, hb⟩ := hs1 (r, j)
    exact ⟨q, A, B, C, hr, hb⟩
  obtain ⟨q, A, B, C, hMM, hlow⟩ := mme_finite_MM_extractions_kronFin_tau_product
    (fun r ↦ kronFin 8 (fun j ↦ sixSymmetrization (P K t (evc r j)))) (790643 / 1000000 : ℝ)
    (fun r ↦ ∏ j : Fin 8, (Real.exp (rq r j : ℝ)) ^ (6 * (t * mass (evc r j))))
    (fun r ↦ by positivity) hext
  obtain ⟨q', A', B', C', hres', hbound'⟩ := finite_parent_of_cyclic_copies
    (original K (t * denominator)) (pieces K t a) (source K t) k (790643 / 1000000 : ℝ) _ hres
    (source_parent K t) ⟨q, A, B, C, hMM.trans (cyclic_pieces_iso K t a ha).2, hlow⟩
  have hden : 1 ≤ denominator := by unfold denominator; norm_num
  have hts : s ≤ t := Nat.le_mul_of_pos_left s hLpos
  have hcut : cutoff ≤ t * denominator := by
    calc cutoff ≤ s := by omega
      _ ≤ t := hts
      _ ≤ t * denominator := Nat.le_mul_of_pos_right t hden
  refine ⟨t * denominator, hcut, ?_, q', A', B', C', hres', ?_⟩
  · rw [parent_len]
    exact hcut.trans (Nat.le_mul_of_pos_left _ (by norm_num))
  · refine (pow_le_pow_left₀ hv.le hvF.le _).trans ((value_bound t k ?_).trans hbound')
    simpa [mul_assoc] using hk

end MME.DWZMA314

end PartN314F

open MME MME.StothersFourth MME.CompleteSplit.CWFourth MME.DWZRestrictedValue
  MME.DWZComponentRestriction
set_option autoImplicit false

theorem solution {K : Type u} [Field K] :
    HasPrescribedZSixRestrictionValueAtLeast
      (cwFourthConstituent K 5 3 1 4)
      (constituentBasis K 5 3 1 4 2)
      (fun a : LiftedCoarseCoordinate.{u} 5 4 ↦ cwSquarePairGrade 5 a.down.val.1)
      DWZPositiveComponent314.parentProfile
      (790643 / 1000000) (Real.exp (1539739919103 / 250000000000)) := by
  have h : ((MME.DWZMA314.Fq : ℚ) : ℝ) = 1539739919103 / 250000000000 := by
    unfold MME.DWZMA314.Fq
    push_cast
    ring
  rw [← h]
  exact MME.DWZMA314.value314
