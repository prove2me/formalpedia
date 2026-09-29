-- Prove2me | solution 1 for mme_recursive_yz_boundary_actual_matrix_extraction
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-13T13:34:38.484049+00:00
-- url     : https://prove2.me/submissions/38d92d68-4952-431c-bc1a-43aa1b9d3c04

import Definitions.Def_mme_recursive_yz_boundary_data
import Theorems.Thm_mme_recursive_yz_boundary_exact_code_card
import Theorems.Thm_mme_restrict_basisAllAllowedSubtensor_of_vanishes
import Mathlib.Algebra.BigOperators.Fin
open MME MME.CompleteSplit MME.TensorObj PiTensorProduct TensorProduct BigOperators Module
  MME.DWZStep1Support MME.RecursiveYZ.CWCells MME.RecursiveYZ.Boundary
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 900000
set_option maxRecDepth 2000
universe u

private theorem interchange_tprod_explicit
    {K : Type u} [Field K] {d : ℕ}
    {V W : Fin d → Type u}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (v : ∀ i, V i) (w : ∀ i, W i) :
    interchange (PiTensorProduct.tprod K v) (PiTensorProduct.tprod K w) =
      PiTensorProduct.tprod K (fun i ↦ v i ⊗ₜ[K] w i) := by
  change (PiTensorProduct.lift interchangeOuter (PiTensorProduct.tprod K v))
      (PiTensorProduct.tprod K w) = _
  rw [PiTensorProduct.lift.tprod]
  change (PiTensorProduct.lift (interchangeInner v)) (PiTensorProduct.tprod K w) = _
  rw [PiTensorProduct.lift.tprod]
  rfl

private theorem interchange_basis_repr_explicit
    {K : Type u} [Field K] {d : ℕ}
    {V W : Fin d → Type u}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    {ι κ : Fin d → Type u}
    (b : ∀ i, Basis (ι i) K (V i))
    (c : ∀ i, Basis (κ i) K (W i))
    (x : PiTensorProduct K V) (y : PiTensorProduct K W)
    (p : ∀ i, ι i) (q : ∀ i, κ i) :
    (Basis.piTensorProduct
        (fun i ↦ Module.Basis.tensorProduct (b i) (c i))).repr
        (interchange x y) (fun i ↦ (p i, q i)) =
      (Basis.piTensorProduct b).repr x p *
        (Basis.piTensorProduct c).repr y q := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod a v =>
      induction y using PiTensorProduct.induction_on with
      | smul_tprod a' w =>
          simp [interchange_tprod_explicit, Finset.prod_mul_distrib]
          ring
      | add y z hy hz =>
          simp only [map_add, Finsupp.add_apply, mul_add, hy, hz]
  | add x z hx hz =>
      simp only [map_add, LinearMap.add_apply, Finsupp.add_apply,
        add_mul, hx, hz]

private theorem piTensorProduct_basis_reindex_explicit
    {K : Type u} [Field K] {d : ℕ}
    {V : Fin d → Type u}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    {ι κ : Fin d → Type u}
    (b : ∀ i, Basis (ι i) K (V i))
    (e : ∀ i, ι i ≃ κ i) :
    Basis.piTensorProduct (fun i ↦ (b i).reindex (e i)) =
      (Basis.piTensorProduct b).reindex (Equiv.piCongrRight e) := by
  ext w
  simp [Basis.piTensorProduct_apply,
    Module.Basis.reindex_apply]

private theorem basis_repr_equiv_explicit
    {K : Type u} [Field K]
    {V W : Type u} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    {ι κ : Type u} (B : Basis ι K V) (C : Basis κ K W) (E : ι ≃ κ)
    (x : V) (w : κ) :
    C.repr (B.equiv C E x) w = B.repr x (E.symm w) := by
  have h := congrArg (fun f : ι →₀ K ↦ f (E.symm w))
    ((C.reindex E.symm).repr.apply_symm_apply (B.repr x))
  change (C.reindex E.symm).repr
    ((C.reindex E.symm).repr.symm (B.repr x)) (E.symm w) = B.repr x (E.symm w) at h
  rw [Module.Basis.repr_reindex_apply] at h
  simpa [Module.Basis.equiv, LinearEquiv.trans_apply] using h

@[simp]
private theorem kronPowModeWordBasis_succ_apply_explicit
    {K : Type u} [Field K] {d : ℕ}
    (T : TensorObj K d) (i : Fin d) {ι : Type u}
    (b : Basis ι K (T.V i)) (n : ℕ) (w : Fin (n + 1) → ι) :
    kronPowModeWordBasis T i b (n + 1) w =
      b (w 0) ⊗ₜ[K]
        kronPowModeWordBasis T i b n (fun r ↦ w r.succ) := by
  rw [kronPowModeWordBasis]
  calc
    _ = (Module.Basis.tensorProduct b
          (kronPowModeWordBasis T i b n))
        ((Fin.consEquiv (fun _ : Fin (n + 1) ↦ ι)).symm w) :=
      Module.Basis.reindex_apply _ _ _
    _ = _ := by
      rw [Fin.consEquiv_symm_apply,
        Module.Basis.tensorProduct_apply]
      rfl

private noncomputable def kronPowTensorWordBasisExplicit
    {K : Type u} [Field K] {d : ℕ}
    (T : TensorObj K d) {ι : Fin d → Type u}
    (b : ∀ i, Basis (ι i) K (T.V i)) (n : ℕ) :
    Basis (∀ i, Fin n → ι i) K
      (PiTensorProduct K (fun i ↦ (T.kronPow n).V i)) :=
  Basis.piTensorProduct
    (fun i ↦ kronPowModeWordBasis T i (b i) n)

private theorem kronPowTensorWordBasis_repr_explicit
    {K : Type u} [Field K] {d : ℕ}
    (T : TensorObj K d) {ι : Fin d → Type u}
    (b : ∀ i, Basis (ι i) K (T.V i))
    (n : ℕ) (w : ∀ i, Fin n → ι i) :
    (kronPowTensorWordBasisExplicit T b n).repr (T.kronPow n).t w =
      ∏ r : Fin n,
        (Basis.piTensorProduct b).repr T.t (fun i ↦ w i r) := by
  induction n with
  | zero =>
      change
        (Basis.piTensorProduct
          (fun i ↦ Basis.singleton (Fin 0 → ι i) K)).repr
            (PiTensorProduct.tprod K (fun _ ↦ (1 : K))) w = 1
      rw [Basis.piTensorProduct_repr_tprod_apply]
      simp only [Module.Basis.singleton_repr, Finset.prod_const_one]
  | succ n ih =>
      change
        (Basis.piTensorProduct
          (fun i ↦
            (Module.Basis.tensorProduct (b i)
              (kronPowModeWordBasis T i (b i) n)).reindex
                (Fin.consEquiv (fun _ : Fin (n + 1) ↦ ι i)))).repr
          (interchange T.t (T.kronPow n).t) w = _
      rw [piTensorProduct_basis_reindex_explicit]
      rw [Module.Basis.repr_reindex_apply]
      rw [interchange_basis_repr_explicit]
      simp only [Equiv.piCongrRight_symm_apply,
        Pi.map_apply, Fin.consEquiv_symm_apply]
      change
        (Basis.piTensorProduct b).repr T.t (fun i ↦ w i 0) *
          (kronPowTensorWordBasisExplicit T b n).repr (T.kronPow n).t
            (fun i r ↦ w i r.succ) = _
      rw [ih]
      rw [Fin.prod_univ_succ]


private theorem select_coeff_restrict
    {K : Type u} [Field K] (T S : TensorObj K 3)
    {I : Fin 3 → Type u} {J : Fin 3 → Type}
    [∀ i, Fintype (J i)]
    (b : ∀ i, Basis (I i) K (T.V i)) (c : ∀ i, Basis (J i) K (S.V i))
    (allowed : ∀ i, I i → Prop) (e : ∀ i, J i → I i)
    (he : ∀ i j, allowed i (e i j))
    (hc : ∀ w, (Basis.piTensorProduct b).repr T.t (fun i ↦ e i (w i)) =
      (Basis.piTensorProduct c).repr S.t w) :
    Restrict S (T.basisAllAllowedSubtensor b allowed) := by
  classical
  let f := fun i ↦ (c i).equivFun.symm.toLinearMap.comp
    (LinearMap.pi (fun j ↦ (b i).coord (e i j)))
  have hf (i : Fin 3) (x : T.V i) (j : J i) :
      (c i).repr (f i x) j = (b i).repr x (e i j) := by
    change (c i).coord j ((c i).equivFun.symm _) = _
    rw [Basis.coord_equivFun_symm]
    rfl
  have hmap (x : PiTensorProduct K T.V) (w : ∀ i, J i) :
      (Basis.piTensorProduct c).repr (PiTensorProduct.map f x) w =
        (Basis.piTensorProduct b).repr x (fun i ↦ e i (w i)) := by
    induction x using PiTensorProduct.induction_on with
    | smul_tprod a v =>
      simp only [map_smul, PiTensorProduct.map_tprod,
        Basis.piTensorProduct_repr_tprod_apply, Finsupp.smul_apply, hf]
    | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
  apply mme_restrict_basisAllAllowedSubtensor_of_vanishes T S b allowed f
  · apply (Basis.piTensorProduct c).repr.injective
    ext w
    exact (hmap T.t w).trans (hc w)
  · intro i x hx
    apply (c i).repr.injective
    ext j
    rw [hf]
    have hne : x ≠ e i j := fun h ↦ hx (h ▸ he i j)
    simp [hne]

private def triple (z : Fin 3) (a b : Fin 7) : Fin 3 → ULift.{u} (Fin 7) :=
  if z = 0 then ![⟨0⟩, ⟨a⟩, ⟨MME.RecursiveYZ.Boundary.flip b⟩]
  else if z = 1 then ![⟨MME.RecursiveYZ.Boundary.flip b⟩, ⟨0⟩, ⟨a⟩]
  else ![⟨a⟩, ⟨MME.RecursiveYZ.Boundary.flip b⟩, ⟨0⟩]

private noncomputable def bbase (K : Type u) [Field K] :
    ∀ i : Fin 3, Basis (ULift.{u} (Fin 7)) K ((CWObj K 5).V i) :=
  fun i ↦ (cwThreeCanonicalBasis K 5 i).reindex Equiv.ulift.symm

private theorem monom_basis {K : Type u} [Field K] (a b c : Fin 7) :
    CWMonom K 5 a b c = (Basis.piTensorProduct (bbase K)) ![ULift.up a,ULift.up b,ULift.up c] := by
  rw [Basis.piTensorProduct_apply]
  unfold CWMonom
  congr 1
  funext i
  fin_cases i <;> dsimp only [bbase, cwThreeCanonicalBasis] <;>
    rw [Basis.reindex_apply]
  · exact (Pi.basisFun_apply K (Fin 7) a).symm
  · exact (Pi.basisFun_apply K (Fin 7) b).symm
  · exact (Pi.basisFun_apply K (Fin 7) c).symm

private theorem base_expansion {K : Type u} [Field K] :
    (CWObj K 5).t =
      (∑ k : Fin 5, (
        (Basis.piTensorProduct (bbase K)) ![ULift.up 0,ULift.up (⟨k.val+1,by omega⟩ : Fin 7),ULift.up ⟨k.val+1,by omega⟩] +
        (Basis.piTensorProduct (bbase K)) ![ULift.up ⟨k.val+1,by omega⟩,ULift.up 0,ULift.up ⟨k.val+1,by omega⟩] +
        (Basis.piTensorProduct (bbase K)) ![ULift.up ⟨k.val+1,by omega⟩,ULift.up ⟨k.val+1,by omega⟩,ULift.up 0])) +
      (Basis.piTensorProduct (bbase K)) ![ULift.up 0,ULift.up 0,ULift.up 6] +
      (Basis.piTensorProduct (bbase K)) ![ULift.up 0,ULift.up 6,ULift.up 0] +
      (Basis.piTensorProduct (bbase K)) ![ULift.up 6,ULift.up 0,ULift.up 0] := by
  simp only [← monom_basis]
  rfl

private theorem base_coeff {K : Type u} [Field K] (z : Fin 3) (a b : Fin 7) :
    (Basis.piTensorProduct (bbase K)).repr
      (CWObj K 5).t (triple.{u} z a b) = if a = b then 1 else 0 := by
  classical
  have h := base_expansion (K := K)
  generalize (Basis.piTensorProduct (bbase K)) = BB at h ⊢
  rw [h]
  simp only [map_add, map_sum, Finsupp.finset_sum_apply, Finsupp.add_apply,
    Basis.repr_self, Finsupp.single_apply]
  clear h
  simp only [Fin.sum_univ_succ]
  fin_cases z <;> fin_cases a <;> fin_cases b <;>
    norm_num [triple, MME.RecursiveYZ.Boundary.flip, Equiv.swap_apply_def,
      Matrix.vecCons_inj, ULift.ext_iff]
  all_goals norm_num [Fin.ext_iff]

private theorem power_coeff {K : Type u} [Field K] (ell L : ℕ) (z : Fin 3)
    (x y : Fin (L * 2 ^ (ell - 1)) → Fin 7) :
    (Basis.piTensorProduct (basis K 5 ell L)).repr (source K 5 ell L).t
      (fun i r ↦ triple z (x r) (y r) i) = if x = y then 1 else 0 := by
  classical
  refine (kronPowTensorWordBasis_repr_explicit (CWObj K 5) (bbase K)
    (L * 2 ^ (ell - 1)) (fun i r ↦ triple.{u} z (x r) (y r) i)).trans ?_
  have hb (a b : Fin 7) := base_coeff (K := K) z a b
  generalize (Basis.piTensorProduct (bbase K)).repr (CWObj K 5).t = coeff at hb ⊢
  change (∏ r, coeff (triple.{u} z (x r) (y r))) = _
  simp only [hb]
  by_cases h : x = y
  · subst y; simp
  · rw [if_neg h]
    obtain ⟨r,hr⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ r) (if_neg hr)

private def flat {ell L : ℕ} {mu : CompleteWord ell → ℕ}
    (x : Code ell L mu) (r : Fin (L * 2 ^ (ell - 1))) : Fin 7 :=
  x.val (finProdFinEquiv.symm r).1 (finProdFinEquiv.symm r).2

private theorem flat_injective {ell L : ℕ} {mu : CompleteWord ell → ℕ} :
    Function.Injective (@flat ell L mu) := by
  intro x y h
  apply Subtype.ext
  funext p r
  have := congrFun h (finProdFinEquiv (p,r))
  simpa [flat] using this

private theorem flip_grade (a : Fin 7) :
    cwSquareCoordGrade 5 (MME.RecursiveYZ.Boundary.flip a) =
      ⟨2 - (cwSquareCoordGrade 5 a).val, by omega⟩ := by
  fin_cases a <;> decide

private theorem flipLabel_twice {ell : ℕ} (s : CompleteWord ell) :
    flipLabel (flipLabel s) = s := by
  funext r
  apply Fin.ext
  simp only [flipLabel]
  omega

private theorem grade_flipLabel {ell : ℕ} (s : CompleteWord ell) :
    MME.RecursiveYZ.CWCells.grade (flipLabel s) = 2 * 2 ^ (ell - 1) - MME.RecursiveYZ.CWCells.grade s := by
  unfold MME.RecursiveYZ.CWCells.grade flipLabel
  rw [Finset.sum_tsub_distrib]
  · simp [mul_comm]
  · intro r _; exact Nat.le_of_lt_succ (s r).isLt

private theorem code_grade {ell L : ℕ} (B : MME.RecursiveYZ.Boundary.Profile ell L)
    (x : Code ell L B.count) (p : Fin L) : MME.RecursiveYZ.CWCells.grade (labels (x.val p)) = B.index := by
  apply B.supported
  have h := x.property (labels (x.val p))
  have hp : 0 < Fintype.card {r : Fin L // labels (x.val r) = labels (x.val p)} :=
    Fintype.card_pos_iff.mpr ⟨⟨p,rfl⟩⟩
  omega

private theorem label_flat {ell L : ℕ} {mu : CompleteWord ell → ℕ}
    (x : Code ell L mu) (p : Fin L) :
    label 5 ell L (Equiv.refl _) (fun r ↦ (⟨flat x r⟩ : ULift.{u} (Fin 7))) p = labels (x.val p) := by
  funext r
  simp [label, flat, labels]

private theorem label_flip_flat {ell L : ℕ} {mu : CompleteWord ell → ℕ}
    (x : Code ell L mu) (p : Fin L) :
    label 5 ell L (Equiv.refl _) (fun r ↦ (⟨MME.RecursiveYZ.Boundary.flip (flat x r)⟩ : ULift.{u} (Fin 7))) p =
      flipLabel (labels (x.val p)) := by
  funext r
  simp [label, flat, labels, flipLabel, flip_grade]

private theorem zero_allowed {ell L : ℕ} (B : MME.RecursiveYZ.Boundary.Profile ell L) :
    allowed 5 ell L (Equiv.refl _) (fun _ ↦ Unit.unit)
      (fun _ _ ↦ 0) (fun _ _ s ↦ if s = (fun _ ↦ 0) then L else 0) 0
      (fun _ ↦ (⟨0⟩ : ULift.{u} (Fin 7))) := by
  classical
  constructor
  · intro p; simp [label, MME.RecursiveYZ.CWCells.grade, cwSquareCoordGrade]
  · intro c s
    cases c
    have hl (p : Fin L) : label 5 ell L (Equiv.refl _) (fun _ ↦ (⟨0⟩ : ULift.{u} (Fin 7))) p = (fun _ ↦ 0) := by
      funext r; rfl
    simp only [MME.RecursiveYZ.count, hl, true_and]
    by_cases hs : s = (fun _ ↦ 0)
    · subst s; simp only [hl, eq_self, Finset.filter_true, Finset.card_univ, Fintype.card_fin, if_true]
    · simp only [hl, hs, Ne.symm hs, if_false, Finset.filter_false, Finset.card_empty]

private theorem free_allowed {ell L : ℕ} (B : MME.RecursiveYZ.Boundary.Profile ell L)
    (x : Code ell L B.count) :
    allowed 5 ell L (Equiv.refl _) (fun _ ↦ Unit.unit)
      (fun _ _ ↦ B.index) (fun _ _ ↦ B.count) 0 (fun r ↦ (⟨flat x r⟩ : ULift.{u} (Fin 7))) := by
  classical
  constructor
  · intro p; rw [label_flat]; exact code_grade B x p
  · intro c s
    cases c
    simpa [MME.RecursiveYZ.count, label_flat, Fintype.card_subtype] using x.property s

private theorem flipped_allowed {ell L : ℕ} (B : MME.RecursiveYZ.Boundary.Profile ell L)
    (x : Code ell L B.count) :
    allowed 5 ell L (Equiv.refl _) (fun _ ↦ Unit.unit)
      (fun _ _ ↦ 2 * 2 ^ (ell - 1) - B.index)
      (fun _ _ s ↦ B.count (flipLabel s)) 0
      (fun r ↦ (⟨MME.RecursiveYZ.Boundary.flip (flat x r)⟩ : ULift.{u} (Fin 7))) := by
  classical
  constructor
  · intro p; rw [label_flip_flat, grade_flipLabel, code_grade]
  · intro c s
    cases c
    have hf (p : Fin L) : flipLabel (labels (x.val p)) = s ↔ labels (x.val p) = flipLabel s := by
      constructor
      · intro h; have := congrArg flipLabel h; simpa [flipLabel_twice] using this
      · intro h; rw [h, flipLabel_twice]
    simpa [MME.RecursiveYZ.count, label_flip_flat, hf, Fintype.card_subtype] using
      x.property (flipLabel s)

private def mmIndex (a b c : ℕ) : Fin 3 → Type
  | ⟨0,_⟩ => Fin a × Fin b
  | ⟨1,_⟩ => Fin b × Fin c
  | ⟨2,_⟩ => Fin c × Fin a

private instance mmIndexFintype (a b c : ℕ) (i : Fin 3) : Fintype (mmIndex a b c i) :=
  match i with
  | ⟨0,_⟩ => by change Fintype (Fin a × Fin b); infer_instance
  | ⟨1,_⟩ => by change Fintype (Fin b × Fin c); infer_instance
  | ⟨2,_⟩ => by change Fintype (Fin c × Fin a); infer_instance

private noncomputable def mmBasis (K : Type u) [Field K] (a b c : ℕ) (i : Fin 3) :
    Basis (mmIndex a b c i) K (MMSpace K a b c i) :=
  match i with
  | ⟨0,_⟩ => Pi.basisFun K (Fin a × Fin b)
  | ⟨1,_⟩ => Pi.basisFun K (Fin b × Fin c)
  | ⟨2,_⟩ => Pi.basisFun K (Fin c × Fin a)

private theorem mm_repr0 {K : Type u} [Field K] (a b c : ℕ)
    (x : MMSpace K a b c 0) (j : mmIndex a b c 0) :
    (mmBasis K a b c 0).repr x j = x j := by
  exact Pi.basisFun_repr K (Fin a × Fin b) x j

private theorem mm_repr1 {K : Type u} [Field K] (a b c : ℕ)
    (x : MMSpace K a b c 1) (j : mmIndex a b c 1) :
    (mmBasis K a b c 1).repr x j = x j := by
  exact Pi.basisFun_repr K (Fin b × Fin c) x j

private theorem mm_repr2 {K : Type u} [Field K] (a b c : ℕ)
    (x : MMSpace K a b c 2) (j : mmIndex a b c 2) :
    (mmBasis K a b c 2).repr x j = x j := by
  exact Pi.basisFun_repr K (Fin c × Fin a) x j

private theorem mm_coeff0 {K : Type u} [Field K] (M : ℕ) (w : ∀ i, mmIndex 1 1 M i) :
    (Basis.piTensorProduct (mmBasis K 1 1 M)).repr (MMObj K 1 1 M).t w =
      if (w 1).2 = (w 2).1 then 1 else 0 := by
  classical
  change (Basis.piTensorProduct (mmBasis K 1 1 M)).repr (MMTensor K 1 1 M) w = _
  simp only [MMTensor, map_sum, Finsupp.finset_sum_apply]
  simp only [Basis.piTensorProduct_repr_tprod_apply]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one]
  change (∑ i : Fin 1, ∑ j : Fin 1, ∑ k : Fin M,
    (mmBasis K 1 1 M 0).repr (Pi.single (i,j) 1) (w 0) *
      ((mmBasis K 1 1 M 1).repr (Pi.single (j,k) 1) (w 1) *
        (mmBasis K 1 1 M 2).repr (Pi.single (k,i) 1) (w 2))) = _
  simp only [mm_repr0 (K := K) 1 1 M, mm_repr1 (K := K) 1 1 M, mm_repr2 (K := K) 1 1 M]
  simp [Fin.eq_zero, Pi.single_apply, Prod.ext_iff, eq_comm, ite_mul, mul_ite]

private theorem mm_coeff1 {K : Type u} [Field K] (M : ℕ) (w : ∀ i, mmIndex M 1 1 i) :
    (Basis.piTensorProduct (mmBasis K M 1 1)).repr (MMObj K M 1 1).t w =
      if (w 2).2 = (w 0).1 then 1 else 0 := by
  classical
  change (Basis.piTensorProduct (mmBasis K M 1 1)).repr (MMTensor K M 1 1) w = _
  simp only [MMTensor, map_sum, Finsupp.finset_sum_apply]
  simp only [Basis.piTensorProduct_repr_tprod_apply]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one]
  change (∑ i : Fin M, ∑ j : Fin 1, ∑ k : Fin 1,
    (mmBasis K M 1 1 0).repr (Pi.single (i,j) 1) (w 0) *
      ((mmBasis K M 1 1 1).repr (Pi.single (j,k) 1) (w 1) *
        (mmBasis K M 1 1 2).repr (Pi.single (k,i) 1) (w 2))) = _
  simp only [mm_repr0 (K := K) M 1 1, mm_repr1 (K := K) M 1 1, mm_repr2 (K := K) M 1 1]
  simp [Fin.eq_zero, Pi.single_apply, Prod.ext_iff, eq_comm, ite_mul, mul_ite]

private theorem mm_coeff2 {K : Type u} [Field K] (M : ℕ) (w : ∀ i, mmIndex 1 M 1 i) :
    (Basis.piTensorProduct (mmBasis K 1 M 1)).repr (MMObj K 1 M 1).t w =
      if (w 0).2 = (w 1).1 then 1 else 0 := by
  classical
  change (Basis.piTensorProduct (mmBasis K 1 M 1)).repr (MMTensor K 1 M 1) w = _
  simp only [MMTensor, map_sum, Finsupp.finset_sum_apply]
  simp only [Basis.piTensorProduct_repr_tprod_apply]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one]
  change (∑ i : Fin 1, ∑ j : Fin M, ∑ k : Fin 1,
    (mmBasis K 1 M 1 0).repr (Pi.single (i,j) 1) (w 0) *
      ((mmBasis K 1 M 1 1).repr (Pi.single (j,k) 1) (w 1) *
        (mmBasis K 1 M 1 2).repr (Pi.single (k,i) 1) (w 2))) = _
  simp only [mm_repr0 (K := K) 1 M 1, mm_repr1 (K := K) 1 M 1, mm_repr2 (K := K) 1 M 1]
  simp [Fin.eq_zero, Pi.single_apply, Prod.ext_iff, eq_comm, ite_mul, mul_ite]

theorem solution {K : Type u} [Field K] {ell L : ℕ}
    (B : MME.RecursiveYZ.Boundary.Profile ell L) (z : Fin 3) :
    Restrict (MMObj K (B.a z) (B.b z) (B.c z)) (B.tensor K z) := by
  classical
  let M := Fintype.card (Code ell L B.count)
  have hd : B.dim = M := (mme_recursive_yz_boundary_exact_code_card B).symm
  let E : Fin M ≃ Code ell L B.count := (Fintype.equivFin _).symm
  have hE : Function.Injective (fun j : Fin M ↦ flat (E j)) :=
    flat_injective.comp E.injective
  have hz := zero_allowed.{u} B
  fin_cases z
  · change Restrict (MMObj K 1 1 B.dim) (B.tensor K 0)
    rw [hd]
    let e : ∀ i, mmIndex 1 1 M i → WordIndex.{u} 5 ell L := by
      intro i
      match i with
      | ⟨0,_⟩ => exact fun j r ↦ ULift.up (0)
      | ⟨1,_⟩ => exact fun j r ↦ ULift.up (flat (E j.2) r)
      | ⟨2,_⟩ => exact fun j r ↦ ULift.up (MME.RecursiveYZ.Boundary.flip (flat (E j.1) r))
    apply select_coeff_restrict (source K 5 ell L) (MMObj K 1 1 M)
      (basis K 5 ell L) (mmBasis K 1 1 M)
      (allowed 5 ell L (Equiv.refl _) (fun _ ↦ Unit.unit)
        (fun _ ↦ B.shape 0) (fun i _ ↦ B.mu 0 i)) e
    · intro i j
      fin_cases i
      · simpa [e, allowed, MME.RecursiveYZ.Boundary.Profile.shape,
          MME.RecursiveYZ.Boundary.Profile.mu] using (hz)
      · simpa [e, allowed, MME.RecursiveYZ.Boundary.Profile.shape,
          MME.RecursiveYZ.Boundary.Profile.mu] using (free_allowed.{u} B (E j.2))
      · simpa [e, allowed, MME.RecursiveYZ.Boundary.Profile.shape,
          MME.RecursiveYZ.Boundary.Profile.mu] using (flipped_allowed.{u} B (E j.1))
    · intro w
      have heq : (fun i ↦ e i (w i)) =
          (fun i r ↦ triple 0 (flat (E (w 1).2) r) (flat (E (w 2).1) r) i) := by
        funext i r
        fin_cases i <;> rfl
      rw [heq, power_coeff]
      simpa only [hE.eq_iff] using (mm_coeff0 (K := K) M w).symm
  · change Restrict (MMObj K B.dim 1 1) (B.tensor K 1)
    rw [hd]
    let e : ∀ i, mmIndex M 1 1 i → WordIndex.{u} 5 ell L := by
      intro i
      match i with
      | ⟨0,_⟩ => exact fun j r ↦ ULift.up (MME.RecursiveYZ.Boundary.flip (flat (E j.1) r))
      | ⟨1,_⟩ => exact fun j r ↦ ULift.up (0)
      | ⟨2,_⟩ => exact fun j r ↦ ULift.up (flat (E j.2) r)
    apply select_coeff_restrict (source K 5 ell L) (MMObj K M 1 1)
      (basis K 5 ell L) (mmBasis K M 1 1)
      (allowed 5 ell L (Equiv.refl _) (fun _ ↦ Unit.unit)
        (fun _ ↦ B.shape 1) (fun i _ ↦ B.mu 1 i)) e
    · intro i j
      fin_cases i
      · simpa [e, allowed, MME.RecursiveYZ.Boundary.Profile.shape,
          MME.RecursiveYZ.Boundary.Profile.mu] using (flipped_allowed.{u} B (E j.1))
      · simpa [e, allowed, MME.RecursiveYZ.Boundary.Profile.shape,
          MME.RecursiveYZ.Boundary.Profile.mu] using (hz)
      · simpa [e, allowed, MME.RecursiveYZ.Boundary.Profile.shape,
          MME.RecursiveYZ.Boundary.Profile.mu] using (free_allowed.{u} B (E j.2))
    · intro w
      have heq : (fun i ↦ e i (w i)) =
          (fun i r ↦ triple 1 (flat (E (w 2).2) r) (flat (E (w 0).1) r) i) := by
        funext i r
        fin_cases i <;> rfl
      rw [heq, power_coeff]
      simpa only [hE.eq_iff] using (mm_coeff1 (K := K) M w).symm
  · change Restrict (MMObj K 1 B.dim 1) (B.tensor K 2)
    rw [hd]
    let e : ∀ i, mmIndex 1 M 1 i → WordIndex.{u} 5 ell L := by
      intro i
      match i with
      | ⟨0,_⟩ => exact fun j r ↦ ULift.up (flat (E j.2) r)
      | ⟨1,_⟩ => exact fun j r ↦ ULift.up (MME.RecursiveYZ.Boundary.flip (flat (E j.1) r))
      | ⟨2,_⟩ => exact fun j r ↦ ULift.up (0)
    apply select_coeff_restrict (source K 5 ell L) (MMObj K 1 M 1)
      (basis K 5 ell L) (mmBasis K 1 M 1)
      (allowed 5 ell L (Equiv.refl _) (fun _ ↦ Unit.unit)
        (fun _ ↦ B.shape 2) (fun i _ ↦ B.mu 2 i)) e
    · intro i j
      fin_cases i
      · simpa [e, allowed, MME.RecursiveYZ.Boundary.Profile.shape,
          MME.RecursiveYZ.Boundary.Profile.mu] using (free_allowed.{u} B (E j.2))
      · simpa [e, allowed, MME.RecursiveYZ.Boundary.Profile.shape,
          MME.RecursiveYZ.Boundary.Profile.mu] using (flipped_allowed.{u} B (E j.1))
      · simpa [e, allowed, MME.RecursiveYZ.Boundary.Profile.shape,
          MME.RecursiveYZ.Boundary.Profile.mu] using (hz)
    · intro w
      have heq : (fun i ↦ e i (w i)) =
          (fun i r ↦ triple 2 (flat (E (w 0).2) r) (flat (E (w 1).1) r) i) := by
        funext i r
        fin_cases i <;> rfl
      rw [heq, power_coeff]
      simpa only [hE.eq_iff] using (mm_coeff2 (K := K) M w).symm
