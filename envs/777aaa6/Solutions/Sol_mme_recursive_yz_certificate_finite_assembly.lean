-- Prove2me | solution 1 for mme_recursive_yz_certificate_finite_assembly
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-12T11:32:44.56966+00:00
-- url     : https://prove2.me/submissions/9c4e537f-f618-4b11-848b-8061a1b1c503

import Definitions.Def_mme_recursive_yz_stage_certificate
import Theorems.Thm_mme_recursive_yz_repaired_CW_extraction
import Theorems.Thm_mme_recursive_yz_simultaneous_usable_incidence
import Theorems.Thm_mme_dwz_asymmetric_hash_AP_free_membership_iff_common_label
import Definitions.Def_mme_tensor_quotient

open BigOperators MME MME.TensorObj MME.CompleteSplit MME.RecursiveYZ
  MME.RecursiveYZ.Certificate MME.HashExtraction
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 800000
universe u

private theorem kron_mono {K : Type u} [Field K] {A A' B B' : TensorObj K 3}
    (ha : Restrict A A') (hb : Restrict B B') : Restrict (A.kron B) (A'.kron B') := by
  let P := TensorQ.tensorStrassen K 3 (by decide)
  have H1 : TensorQ.le (TensorQ.toQ A * TensorQ.toQ B) (TensorQ.toQ A' * TensorQ.toQ B) :=
    P.mul_right _ _ ha _
  have H2 : TensorQ.le (TensorQ.toQ A' * TensorQ.toQ B) (TensorQ.toQ A' * TensorQ.toQ B') := by
    simpa only [mul_comm] using P.mul_right (TensorQ.toQ B) (TensorQ.toQ B') hb (TensorQ.toQ A')
  exact H1.trans H2

private theorem kronFin_mono {K : Type u} [Field K] {k : ℕ}
    (A B : Fin k → TensorObj K 3) (h : ∀ j, Restrict (A j) (B j)) :
    Restrict (kronFin k A) (kronFin k B) := by
  induction k with
  | zero => exact Restrict.refl _
  | succ k ih => exact kron_mono (h 0) (ih _ _ (fun j ↦ h j.succ))

private theorem bucket_eq (D : HashData) (q : D.State) :
    RecursiveXHash.hashed D.m D.positions (D.labels.image (fun a : ℕ ↦ (a : ZMod D.p))) q = D.retained q := by
  classical
  letI : Fact D.p.Prime := ⟨D.prime⟩
  ext w
  simp only [RecursiveXHash.hashed,HashData.retained,RecursiveXHash.bucketed,Finset.mem_filter]
  have hs (t : Fin (D.N + 1)) :
      RecursiveXHash.fieldWord D.p D.positions 0 w t + RecursiveXHash.fieldWord D.p D.positions 1 w t +
        RecursiveXHash.fieldWord D.p D.positions 2 w t = (D.half : ZMod D.p) := by
    have H := (w (D.positions t).1 (D.positions t).2).property.1
    change (((w (D.positions t).1 (D.positions t).2).val 0).val : ZMod D.p) +
      (((w (D.positions t).1 (D.positions t).2).val 1).val : ZMod D.p) +
      (((w (D.positions t).1 (D.positions t).2).val 2).val : ZMod D.p) = _
    simpa only [Nat.cast_add] using congrArg (fun a : ℕ ↦ (a : ZMod D.p)) H
  have H := mme_dwz_asymmetric_hash_AP_free_membership_iff_common_label D.odd D.labels D.labels_range D.labels_free
    (D.half : ZMod D.p) (RecursiveXHash.fieldWord D.p D.positions 0 w)
    (RecursiveXHash.fieldWord D.p D.positions 1 w) (RecursiveXHash.fieldWord D.p D.positions 2 w) hs q
  exact and_congr_right (fun _ ↦ H.symm)

private theorem stage_budget (D : HashData) (A : Stage D) (hA : A.Budget) : D.Budget := by
  classical
  letI : Fact D.p.Prime := ⟨D.prime⟩
  refine ⟨hA.1,?_⟩
  let castS := D.labels.image (fun a : ℕ ↦ (a : ZMod D.p))
  have hcast : castS.card = D.labels.card := by
    apply Finset.card_image_iff.mpr
    intro a ha b hb hab
    have ha' : a < D.p := (Finset.mem_range.mp (D.labels_range ha)).trans_le (Nat.div_le_self _ _)
    have hb' : b < D.p := (Finset.mem_range.mp (D.labels_range hb)).trans_le (Nat.div_le_self _ _)
    have hv := congrArg ZMod.val hab
    simpa only [ZMod.val_natCast_of_lt ha',ZMod.val_natCast_of_lt hb'] using hv
  have H := mme_recursive_yz_simultaneous_usable_incidence D.parent D.n A.total D.m D.positions castS
    D.odd D.grade_lt A.repairScale (fun i ↦ A.mu (yzMode i)) (fun i c ↦ A.mass (yzMode i) c)
    A.keep hA.2.1 hA.2.2
  rw [hcast] at H
  have HR : (7 : ℝ) * (RecursiveXHash.target (n := D.n) D.m).card * D.labels.card * (D.p : ℝ) ^ (D.N + 1) ≤
      8 * ∑ q : D.State,
        ((((RecursiveXHash.target D.m).filter (fun a ↦ a ∈ RecursiveXHash.hashed D.m D.positions castS q)) ∩
          usable A.total D.m D.positions castS q A.repairScale (fun i ↦ A.mu (yzMode i)) A.keep).card : ℝ) := by
    exact_mod_cast H
  simp only [castS,← A.good_eq,bucket_eq] at HR
  linarith

private theorem stage_selected {K : Type u} [Field K] (D : HashData) (A : Stage D)
    (q : D.State) (I : Finset D.Edge) (hI : D.Selection q I) :
    Restrict (bigAdd (fun _ : Fin (I.card / 8 ^ A.repairExponent) ↦ A.template K)) (A.raw K) := by
  classical
  let address : Fin I.card → D.Edge := fun j ↦ ((I.equivFin).symm j).val
  have hmem (j) : address j ∈ I := ((I.equivFin).symm j).property
  have hinj : Function.Injective address := fun a b h ↦ (I.equivFin).symm.injective (Subtype.ext h)
  have hhash (j) : address j ∈ RecursiveXHash.hashed D.m D.positions
      (D.labels.image (fun a : ℕ ↦ (a : ZMod D.p))) q := by
    rw [bucket_eq]
    exact hI.2.1 (hmem j)
  have hholes (j i) : 4 * A.repairScale * (filterHoles A.total D.m D.positions
      (D.labels.image (fun a : ℕ ↦ (a : ZMod D.p))) q i (A.mu (yzMode i))
      (address j) (A.keep i (address j))).card ≤
        (unbrokenWords A.total (yzMode i) (address j) (A.mu (yzMode i))).card := by
    have H := hI.2.2.1 (hmem j)
    rw [A.good_eq] at H
    exact (Finset.mem_filter.mp H).2 i
  exact mme_recursive_yz_repaired_CW_extraction (K := K) 5 A.ell D.half D.R D.N D.p A.L
    A.repairScale A.repairExponent I.card D.parent D.n A.total A.half_eq D.m D.positions A.positions
    (D.labels.image (fun a : ℕ ↦ (a : ZMod D.p))) q A.reference A.reference_target address hinj
    (fun j ↦ hI.1 (hmem j)) (fun j ↦ hI.2.1 (hmem j)) hhash
    (fun j b hb hh ↦ hI.2.2.2 (address j) (hmem j) b hb hh) A.mu A.boundary
    (fun i j ↦ A.keep i (address j)) hholes A.capacity

theorem solution {K : Type u} [Field K] (D : HashExtraction.Data)
    (A : ∀ j, Stage (D.hash j)) (hA : ∀ j, (A j).Budget) :
    (∀ j, (D.hash j).Budget) ∧ (RecursiveAssembly D A K → D.Realizes K) := by
  refine ⟨fun j ↦ stage_budget (D.hash j) (A j) (hA j),?_⟩
  intro H q I hI hsize
  have hextract := kronFin_mono
    (fun j ↦ bigAdd (fun _ : Fin ((I j).card / 8 ^ (A j).repairExponent) ↦ (A j).template K))
    (fun j ↦ (A j).raw K) (fun j ↦ stage_selected (D.hash j) (A j) (q j) (I j) (hI j))
  exact (H.2 (fun j ↦ (I j).card) hsize).trans (hextract.trans H.1)
