-- Prove2me | solution 1 for mme_more_asymmetry_recursive_assembly_of_compatible_data_forward
-- status  : ACCEPTED   (disprove)
-- author  : @Robertboy18
-- created : 2026-09-22T09:28:58.337921+00:00
-- url     : https://prove2.me/submissions/a3a705f6-017e-43f0-9565-7f5623098f0a

import Definitions.Def_mme_tensor_bridge
import Definitions.Def_mme_recursive_yz_stage_certificate
import Definitions.Def_mme_more_asymmetry_raw_source_compatibility
import Definitions.Def_mme_more_asymmetry_template_mm_compatibility

open BigOperators MME MME.RecursiveYZ MME.RecursiveYZ.Certificate MME.CompleteSplit
namespace MME.RecursiveYZ

/-- A positive histogram entry with the wrong grade makes a cell-word block empty. -/
theorem cellWord_isEmpty_of_incompatible_grade
    {P C W D : Type*} [Fintype P]
    (cell : P → C) (grade : W → D) (shape : C → D) (mu : C → W → ℕ)
    (c : C) (w : W) (hmu : 0 < mu c w) (hgrade : grade w ≠ shape c) :
    IsEmpty (CellWord cell grade shape mu) := by
  classical
  constructor
  intro f
  have hcount : 0 < count cell f.val c w := by
    rw [f.property.2 c w]
    exact hmu
  obtain ⟨p, hp⟩ := Finset.card_pos.mp hcount
  have hp' : cell p = c ∧ f.val p = w := (Finset.mem_filter.mp hp).2
  exact hgrade (by simpa only [hp'.1, hp'.2] using f.property.1 p)

end MME.RecursiveYZ


namespace RecursiveBoundaryStageAudit

abbrev parent : Fin 1 → Fin 3 → ℕ := fun _ => ![4, 0, 0]
abbrev Split := MME.RecursiveThinSplit.Split 2 (parent 0)

def split : Split := ⟨![2, 0, 0], by decide⟩

instance : Unique Split where
  default := split
  uniq a := by
    apply Subtype.ext
    funext i
    have h1 := a.property.2 1
    have h2 := a.property.2 2
    have hs := a.property.1
    change (a.val 1).val ≤ 0 at h1
    change (a.val 2).val ≤ 0 at h2
    fin_cases i <;> apply Fin.ext <;> simp [split] <;> omega

def total (r : Fin 1) : parent r 0 + parent r 1 + parent r 2 = 2 * 2 := rfl

abbrev center : CompleteWord 1 := fun _ => 1

noncomputable def mu (_ : Fin 3) (_ : Cell 2 1 parent) (w : CompleteWord 1) : ℕ :=
  if w = center then 2 else 0

theorem center_reverse (w : CompleteWord 1) :
    (fun r => Fin.rev (w r)) = center ↔ w = center := by
  constructor
  · intro h
    funext r
    have hr := congrFun h r
    have hv := congrArg Fin.val hr
    have hb := (w r).isLt
    apply Fin.ext
    simp only [Fin.val_rev, center, Fin.val_one] at hv
    change (w r).val = 1
    omega
  · rintro rfl
    rfl

theorem boundary : BoundaryProfiles mu := by
  have h : ∀ i j c w, mu i c w = mu j c (fun r => Fin.rev (w r)) := by
    intro i j c w
    simp only [mu, center_reverse]
  exact ⟨fun c _ w => h 1 0 c w, fun c _ w => h 2 1 c w,
    fun c _ w => h 2 0 c w⟩

theorem mass (i : Fin 3) (c : Cell 2 1 parent) :
    ∑ w, mu i c w = 1 + 1 := by
  classical
  simp [mu]


def parentPositions : Fin 1 ≃ (_ : Fin 1) × Fin 1 where
  toFun x := ⟨x, 0⟩
  invFun x := x.1
  left_inv _ := rfl
  right_inv x := by ext <;> simp [Subsingleton.elim x.2 0]

def childPositions : Fin 2 ≃ Position (fun _ : Fin 1 => 1) where
  toFun x := ⟨0, 0, x⟩
  invFun x := x.2.2
  left_inv _ := rfl
  right_inv x := by
    rcases x with ⟨r, t, h⟩
    have hr : r = 0 := Subsingleton.elim _ _
    have ht : t = 0 := Subsingleton.elim _ _
    subst r; subst t
    rfl

noncomputable def hash : HashExtraction.HashData where
  half := 2
  R := 1
  parent := parent
  n := fun _ => 1
  m := fun _ _ => 1
  N := 0
  p := 3
  prime := by decide
  odd := by decide
  grade_lt := by decide
  positions := parentPositions
  labels := ∅
  labels_range := Finset.empty_subset _
  labels_free := by simp
  good state := usable total (fun _ _ => 1) parentPositions ∅ state 1
    (fun i => mu (yzMode i)) (fun _ _ _ => True)

def reference : hash.Edge := fun _ _ => split

theorem reference_target : reference ∈ RecursiveXHash.target hash.m := by
  classical
  simp only [RecursiveXHash.target, Finset.mem_filter, Finset.mem_univ, true_and]
  intro r a
  have ha : a = split := @Subsingleton.elim Split inferInstance a split
  subst a
  simp [MME.RecursiveThinSplit.count, hash, reference]

instance block_empty : IsEmpty
    (CWCells.Block 1 (fullCell total reference)
      (fun c i => (c.2.val i).val) mu 0) := by
  apply cellWord_isEmpty_of_incompatible_grade
    (c := (⟨0, split⟩ : Cell 2 1 parent)) (w := center)
  · norm_num [mu]
  · norm_num [CWCells.grade, center, split]

noncomputable def stage : Stage hash where
  ell := 1
  L := 2
  repairScale := 1
  repairExponent := 0
  total := total
  half_eq := rfl
  positions := childPositions
  mu := mu
  boundary := boundary
  mass := mass
  reference := reference
  reference_target := reference_target
  keep := fun _ _ _ => True
  good_eq := by intro state; simp [hash]
  capacity := by
    have h : Nat.card (CWCells.Block 1 (fullCell total reference)
        (fun c i => (c.2.val i).val) mu 0) = 0 := Nat.card_of_isEmpty
    change (∏ i : Fin 3, Nat.card (CWCells.Block 1 (fullCell total reference)
      (fun c i => (c.2.val i).val) mu i)) < 1
    rw [Fin.prod_univ_three, h]
    simp

theorem not_allowed (x : CWCells.WordIndex 5 1 2) :
    ¬ CWCells.allowed 5 1 2 childPositions (fullCell total reference)
      (fun c i => (c.2.val i).val) mu 0 x := by
  intro hx
  exact isEmptyElim (⟨CWCells.label 5 1 2 childPositions x, hx⟩ :
    CWCells.Block 1 (fullCell total reference) (fun c i => (c.2.val i).val) mu 0)

theorem template_x_zero (K : Type*) [Field K] (v : (stage.template K).V 0) : v = 0 := by
  classical
  apply Subtype.ext
  have hv := v.property
  change v.val ∈ cwBasisGrade (CWCells.basis K 5 1 2 0)
    (fun j => if CWCells.allowed 5 1 2 childPositions (fullCell total reference)
      (fun c i => (c.2.val i).val) mu 0 j then (0 : Fin 2) else 1) 0 at hv
  have hz : v.val ∈ (⊥ : Submodule K ((CWCells.source K 5 1 2).V 0)) := by
    simpa [cwBasisGrade, not_allowed] using hv
  exact (Submodule.mem_bot K).mp hz

theorem template_tensor_zero (K : Type*) [Field K] : (stage.template K).t = 0 := by
  generalize (stage.template K).t = t
  induction t using PiTensorProduct.induction_on with
  | smul_tprod c f =>
    rw [MultilinearMap.map_coord_zero (PiTensorProduct.tprod K) 0
      (template_x_zero K (f 0)), smul_zero]
  | add x y hx hy => simp [hx, hy]

noncomputable def cwFunctional (K : Type*) [Field K] (i : Fin 3) :
    (CWObj K 5).V i →ₗ[K] K :=
  match i with
  | ⟨0, _⟩ => LinearMap.proj 0
  | ⟨1, _⟩ => LinearMap.proj 0
  | ⟨2, _⟩ => LinearMap.proj 6

theorem cw_one_restrict (K : Type*) [Field K] :
    TensorObj.Restrict (TensorObj.oneObj : TensorObj K 3) (CWObj K 5) := by
  classical
  letI : ∀ i, AddCommGroup (CWSpace K 5 i) := CWSpace_addCommGroup 5
  letI : ∀ i, Module K (CWSpace K 5 i) := CWSpace_module 5
  have hp (v : Fin 3 → K) : PiTensorProduct.tprod K v =
      (∏ i, v i) • PiTensorProduct.tprod K (fun _ : Fin 3 => (1 : K)) := by
    simpa using (PiTensorProduct.tprod K (s := fun _ : Fin 3 => K)).map_smul_univ
      v (fun _ => (1 : K))
  let F : PiTensorProduct K (CWSpace K 5) →ₗ[K]
      PiTensorProduct K (fun _ : Fin 3 => K) := PiTensorProduct.map (cwFunctional K)
  have hm (a b c : Fin 7) : F (CWMonom K 5 a b c) =
      ((if a = 0 then (1 : K) else 0) * (if b = 0 then 1 else 0) *
        (if c = 6 then 1 else 0)) •
        PiTensorProduct.tprod K (fun _ : Fin 3 => (1 : K)) := by
    have hmap := PiTensorProduct.map_tprod (cwFunctional K)
      (fun s : Fin 3 => match s with
        | ⟨0, _⟩ => (Pi.single a 1 : Fin 7 → K)
        | ⟨1, _⟩ => (Pi.single b 1 : Fin 7 → K)
        | ⟨2, _⟩ => (Pi.single c 1 : Fin 7 → K))
    change F (CWMonom K 5 a b c) = _ at hmap
    rw [hmap, hp]
    rw [Fin.prod_univ_three]
    change ((Pi.single a (1 : K) : Fin 7 → K) 0 *
      (Pi.single b (1 : K) : Fin 7 → K) 0 *
      (Pi.single c (1 : K) : Fin 7 → K) 6) • _ = _
    simp [Pi.single_apply, eq_comm]
  refine ⟨cwFunctional K, ?_⟩
  change F (CWTensor K 5) = PiTensorProduct.tprod K (fun _ : Fin 3 => (1 : K))
  simp only [CWTensor, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, F.map_add, hm]
  norm_num [Fin.ext_iff]

open TensorQ in
theorem quotient_mul_mono {K : Type*} [Field K]
    {a b c d : TensorQ K 3} (hab : le a b) (hcd : le c d) : le (a * c) (b * d) := by
  let S := tensorStrassen K 3 (by decide)
  exact le_trans _ _ _ (S.mul_right a b hab c)
    (by simpa only [mul_comm] using S.mul_right c d hcd b)

open TensorQ in
theorem quotient_le_mul {K : Type*} [Field K]
    (a : TensorQ K 3) {b : TensorQ K 3} (hb : le 1 b) : le a (a * b) := by
  simpa only [mul_one] using quotient_mul_mono (le_refl a) hb

theorem cyclic_eq_public {K : Type*} [Field K] (X : TensorObj K 3) :
    cyclicSymmetrization X = TensorObj.kron X
      (TensorObj.kron (TensorObj.permObj cyclicPerm X)
        (TensorObj.permObj (cyclicPerm.trans cyclicPerm) X)) := by
  unfold cyclicSymmetrization
  congr 3 <;> apply Equiv.ext <;> intro i <;> fin_cases i <;> rfl

open TensorQ in
theorem raw_restrict_source (K : Type*) [Field K] :
    TensorObj.Restrict (stage.raw K) (sixSymmetrization (StothersFourth.cwFourthObj K 5)) := by
  let x := toQ (CWObj K 5)
  let f := toQ (StothersFourth.cwFourthObj K 5)
  let c := toQ (cyclicSymmetrization (StothersFourth.cwFourthObj K 5))
  have h1 : le 1 x := cw_one_restrict K
  have h2 : le 1 (x * x) := by simpa only [one_mul] using quotient_mul_mono h1 h1
  have h4 : le 1 f := by simpa only [one_mul] using quotient_mul_mono h2 h2
  have hp (e : Equiv.Perm (Fin 3)) : le 1 (permAut e f) := by
    simpa only [map_one] using permAut_le e h4
  have hrest : le 1 (permAut cyclicPerm f * permAut (cyclicPerm.trans cyclicPerm) f) := by
    simpa only [one_mul] using quotient_mul_mono (hp cyclicPerm) (hp (cyclicPerm.trans cyclicPerm))
  have hcq : c = f * (permAut cyclicPerm f * permAut (cyclicPerm.trans cyclicPerm) f) := by
    dsimp only [c]
    rw [cyclic_eq_public]
    rfl
  have hc : le 1 c := by
    rw [hcq]
    simpa only [one_mul] using quotient_mul_mono h4 hrest
  have hfc : le f c := by
    rw [hcq]
    exact quotient_le_mul f hrest
  have hcs : le c (toQ (sixSymmetrization (StothersFourth.cwFourthObj K 5))) :=
    quotient_le_mul c (by simpa only [map_one] using permAut_le swapFirstTwoPerm hc)
  have hxf : le (x * x) f := quotient_le_mul (x * x) h2
  have hxs := le_trans _ _ _ hxf (le_trans _ _ _ hfc hcs)
  change le (x * (x * 1)) (toQ (sixSymmetrization (StothersFourth.cwFourthObj K 5)))
  simpa only [mul_one] using hxs

noncomputable def data : HashExtraction.Data where
  factors := 1
  hash := fun _ => hash
  repairCopies := 1
  repair_pos := by decide
  a := 1
  b := 1
  c := 1
  power := 1

noncomputable def stages : ∀ j, Stage (data.hash j) := fun _ => stage

noncomputable def rawCompatibility (K : Type*) [Field K] :
    MoreAsymmetryRawSourceCompatibility data stages K where
  source := sixSymmetrization (StothersFourth.cwFourthObj K 5)
  factor_restrict := fun _ => raw_restrict_source K
  ambient_isomorphic := TensorObj.Isomorphic.refl _

/-- Every zero tensor is a restriction of every source tensor. -/
theorem zero_restrict {K : Type*} [Field K] (X Y : TensorObj K 3)
    (hX : X.t = 0) : TensorObj.Restrict X Y := by
  refine ⟨fun _ => 0, ?_⟩
  have hz : PiTensorProduct.map (fun i => (0 : Y.V i →ₗ[K] X.V i)) =
      (0 : PiTensorProduct K Y.V →ₗ[K] PiTensorProduct K X.V) := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro v
    simp only [LinearMap.compMultilinearMap_apply, PiTensorProduct.map_tprod,
      LinearMap.zero_apply]
    exact MultilinearMap.map_coord_zero (PiTensorProduct.tprod K) 0 rfl
  rw [hz, LinearMap.zero_apply, hX]

theorem quotient_zero {K : Type*} [Field K] (X : TensorObj K 3)
    (hX : X.t = 0) : TensorQ.toQ X = 0 := by
  apply TensorQ.toQ_eq_iff.mpr
  exact ⟨zero_restrict X TensorObj.zeroObj hX,
    zero_restrict TensorObj.zeroObj X rfl⟩

noncomputable def templateCompatibility (K : Type*) [Field K] :
    MoreAsymmetryTemplateMMCompatibility data stages K where
  localA := fun _ => 1
  localB := fun _ => 1
  localC := fun _ => 1
  factor_restrict := fun _ => zero_restrict _ _ (template_tensor_zero K)
  product_a := by simp [data]
  product_b := by simp [data]
  product_c := by simp [data]

theorem kron_one_iso {K : Type*} [Field K] (X : TensorObj K 3) :
    TensorObj.Isomorphic (TensorObj.kron X TensorObj.oneObj) X := by
  apply TensorQ.toQ_eq_iff.mp
  exact mul_one (TensorQ.toQ X)

theorem copy_iso (K : Type*) [Field K] (counts : Fin data.factors → ℕ) :
    TensorObj.Isomorphic
      (TensorObj.bigAdd (fun _ : Fin ((∏ j, counts j) / data.repairCopies) =>
        MMObj K data.a data.b data.c))
      (TensorObj.kronFin data.factors (fun j =>
        TensorObj.bigAdd (fun _ : Fin (counts j / 8 ^ (stages j).repairExponent) =>
          MMObj K ((templateCompatibility K).localA j)
            ((templateCompatibility K).localB j) ((templateCompatibility K).localC j)))) := by
  change Fin 1 → ℕ at counts
  let T (n : ℕ) := TensorObj.bigAdd (fun _ : Fin n => MMObj K 1 1 1)
  change TensorObj.Isomorphic (T ((∏ j : Fin 1, counts j) / 1))
    (TensorObj.kron (T (counts 0 / 8 ^ 0)) TensorObj.oneObj)
  have he : (∏ j : Fin 1, counts j) / 1 = counts 0 / 8 ^ 0 := by simp
  rw [he]
  exact (kron_one_iso (T (counts 0 / 8 ^ 0))).symm


theorem no_assembly (K : Type*) [Field K] : ¬ RecursiveAssembly data stages K := by
  intro h
  have hl : ∀ j, (data.hash j).lower ≤ ((1 : ℕ) : ℝ) := by
    intro j
    simp [data, hash, HashExtraction.HashData.lower]
  have hr := h.2 (fun _ => 1) hl
  have hz : TensorQ.toQ (stage.template K) = 0 :=
    quotient_zero _ (template_tensor_zero K)
  change TensorObj.Restrict (TensorObj.bigAdd
    (fun _ : Fin ((∏ _ : Fin 1, 1) / 1) => MMObj K 1 1 1))
    (TensorObj.kron (TensorObj.bigAdd
      (fun _ : Fin (1 / 8 ^ 0) => stage.template K)) TensorObj.oneObj) at hr
  change TensorQ.le (MMq K 1 1 1) (TensorQ.toQ (stage.template K) * 1) at hr
  rw [MMq_one, hz, zero_mul] at hr
  have hn : (1 : ℕ) ≤ 0 := ((tensorPreorder K).nat_order_embedding 1 0).mp (by
    simpa only [Nat.cast_one, Nat.cast_zero] using hr)
  omega

end RecursiveBoundaryStageAudit

open RecursiveBoundaryStageAudit
theorem solution : ¬ (∀ (K : Type) [Field K]
    (D : HashExtraction.Data)
    (A : ∀ j, Stage (D.hash j))
    (hraw : MoreAsymmetryRawSourceCompatibility D A K)
    (htemplate : MoreAsymmetryTemplateMMCompatibility D A K)
    (hcopy :
      ∀ counts : Fin D.factors → ℕ,
        (∀ j, (D.hash j).lower ≤ (counts j : ℝ)) →
        TensorObj.Restrict
          (TensorObj.kronFin D.factors
            (fun j ↦ TensorObj.bigAdd
              (fun _ : Fin (counts j / 8 ^ (A j).repairExponent) ↦
                MMObj K (htemplate.localA j) (htemplate.localB j)
                  (htemplate.localC j))))
          (TensorObj.bigAdd
            (fun _ : Fin ((∏ j, counts j) / D.repairCopies) ↦
              MMObj K D.a D.b D.c)))  , 
    RecursiveAssembly D A K) := by
  intro h
  exact no_assembly ℚ (h ℚ data stages (rawCompatibility ℚ)
    (templateCompatibility ℚ) (fun counts _ => (copy_iso ℚ counts).2))
#print axioms solution
