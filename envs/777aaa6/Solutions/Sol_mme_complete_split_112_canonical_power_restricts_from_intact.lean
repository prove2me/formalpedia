-- Prove2me | solution 1 for mme_complete_split_112_canonical_power_restricts_from_intact
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T10:54:02.862611+00:00
-- url     : https://prove2.me/submissions/7b79247f-ce0b-4c60-998f-ad0a94d9d1de

import Definitions.Def_mme_complete_split_112_canonical_source_data
import Definitions.Def_mme_recursive_yz_CW_cells
import Definitions.Def_mme_TypeGrading_kron
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Theorems.Thm_mme_restrict_basisAllAllowedSubtensor_of_vanishes
universe u v w

open MME MME.CompleteSplit MME.CompleteSplit112 MME.DWZComponentRestriction
  MME.RecursiveYZ MME.RecursiveYZ.CWCells
set_option autoImplicit false

namespace MME.CompleteSplit112

/-- Expand each canonical square coordinate into its two elementary CW coordinates. -/
def flattenCoordinate {q N : ℕ} {i : Fin 3}
    (w : PowIndex (CanonicalCoord.{u} q i) N) : WordIndex.{u} q 2 N :=
  fun r ↦ let pr := finProdFinEquiv.symm r
    ⟨(![(PowIndex.get N w pr.1).down.val.1,
        (PowIndex.get N w pr.1).down.val.2] : Fin 2 → Fin (q + 2)) pr.2⟩

theorem flattenCoordinate_label {q N : ℕ} {i : Fin 3}
    (w : PowIndex (CanonicalCoord.{u} q i) N) (p : Fin N) :
    label q 2 N (Equiv.refl _) (flattenCoordinate w) p =
      canonicalLabel q i (PowIndex.get N w p) := by
  funext r
  fin_cases r <;> simp [label, flattenCoordinate, canonicalLabel]

theorem canonicalLabel_grade {q : ℕ} {i : Fin 3}
    (p : CanonicalCoord.{u} q i) :
    grade (canonicalLabel q i p) = (cwSquareBlockType 1 1 2 i).val := by
  have h := congrArg Fin.val p.down.property
  simpa [CWCells.grade, canonicalLabel, cwSquarePairGrade, Fin.sum_univ_succ] using h

/-- Expanding square coordinates preserves the full complete-word histogram. -/
theorem flattenCoordinate_count {q N : ℕ} {i : Fin 3}
    (w : PowIndex (CanonicalCoord.{u} q i) N) (sigma : CompleteWord 2) :
    count (fun _ : Fin N ↦ Unit.unit)
      (label q 2 N (Equiv.refl _) (flattenCoordinate w)) Unit.unit sigma =
      wordCount (canonicalLabel q i) w sigma := by
  classical
  simp only [count, wordCount, flattenCoordinate_label, true_and]

/-- The exact canonical profile predicate becomes the literal intact-block predicate. -/
theorem flattenCoordinate_allowed_iff {q N : ℕ} {i : Fin 3}
    (beta : Profile 2) (mu : CompleteWord 2 → ℕ)
    (hmu : ∀ sigma, (mu sigma : ℝ) = (N : ℝ) * beta.probability sigma)
    (w : PowIndex (CanonicalCoord.{u} q i) N) :
    allowed q 2 N (Equiv.refl _) (fun _ ↦ Unit.unit)
      (fun _ j ↦ (cwSquareBlockType 1 1 2 j).val) (fun _ _ ↦ mu) i
      (flattenCoordinate w) ↔ ApproxConsistent (canonicalLabel q i) beta 0 w := by
  classical
  have hg : ∀ p, grade (label q 2 N (Equiv.refl _) (flattenCoordinate w) p) =
      (cwSquareBlockType 1 1 2 i).val := by
    intro p
    rw [flattenCoordinate_label, canonicalLabel_grade]
  constructor
  · intro h sigma
    have hc := h.2 Unit.unit sigma
    rw [flattenCoordinate_count] at hc
    simp only [NNReal.coe_zero, mul_zero]
    rw [hc, hmu, sub_self, abs_zero]
  · intro h
    refine ⟨hg, ?_⟩
    intro c sigma
    cases c
    rw [flattenCoordinate_count]
    have hc := h sigma
    simp only [NNReal.coe_zero, mul_zero, abs_nonpos_iff, sub_eq_zero] at hc
    exact_mod_cast hc.trans (hmu sigma).symm

end MME.CompleteSplit112


open MME MME.CompleteSplit112 MME.DWZComponentRestriction Module PiTensorProduct
set_option autoImplicit false

namespace MME.CompleteSplit112

private theorem basis_eq_mpr_coe {K : Type u} [Field K]
    {V : Type u} [AddCommGroup V] [Module K V] {I : Type*}
    {S T : Submodule K V} (hST : S = T)
    (h : Basis I K S = Basis I K T) (b : Basis I K T) (j : I) :
    ((Eq.mpr h b) j).val = (b j).val := by
  subst T
  rfl

private theorem canonicalBasis_coe (K : Type u) [Field K] (q : ℕ) (i : Fin 3)
    (p : CanonicalCoord.{u} q i) :
    (canonicalBasis K q i p).val =
      cwSquareCanonicalBasis K q i p.down.val := by
  unfold canonicalBasis
  erw [Basis.reindex_apply]
  have hs : cwBasisGrade (cwSquareCanonicalBasis K q i) (cwSquarePairGrade q)
      (cwSquareBlockType 1 1 2 i) = Submodule.span K
      (Set.range (fun a : CoarsePair q (cwSquareBlockType 1 1 2 i) ↦
        cwSquareCanonicalBasis K q i a.val)) := by
    unfold cwBasisGrade
    congr 1
    ext x
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, ha⟩, rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨a.val, a.property, rfl⟩
  simp only [coarseClassBasis, id_eq]
  erw [basis_eq_mpr_coe hs]
  exact Basis.span_apply _ _

private theorem canonical_projection_coord (K : Type u) [Field K] (q : ℕ) (i : Fin 3)
    (p : CanonicalCoord.{u} q i) (x : ((CWObj K q).kron (CWObj K q)).V i) :
    (canonicalBasis K q i).repr
      ((cwSquareCanonicalGrading K q).blockProj i (cwSquareBlockType 1 1 2 i) x) p =
      (cwSquareCanonicalBasis K q i).repr x p.down.val := by
  classical
  dsimp only [canonicalObj, TensorObj.TypeGrading.blockSubtensor] at *
  let G := cwSquareCanonicalGrading K q
  let b := cwSquareCanonicalBasis K q i
  have hm : ((canonicalBasis K q i).coord p).comp
      (G.blockProj i (cwSquareBlockType 1 1 2 i)) = b.coord p.down.val := by
    apply b.ext
    intro a
    have hmem : b a ∈ G.classOf i (cwSquarePairGrade q a) :=
      Submodule.subset_span ⟨a, rfl, rfl⟩
    by_cases ha : cwSquarePairGrade q a = cwSquareBlockType 1 1 2 i
    · let pa : CanonicalCoord.{u} q i := ⟨⟨a, ha⟩⟩
      have hp : G.blockProj i (cwSquareBlockType 1 1 2 i) (b a) =
          canonicalBasis K q i pa := by
        apply Subtype.val_injective
        rw [canonicalBasis_coe]
        have h := G.blockProj_apply_mem i (cwSquareBlockType 1 1 2 i) (b a)
          (ha ▸ hmem)
        exact congrArg Subtype.val h
      change (canonicalBasis K q i).repr
        (G.blockProj i (cwSquareBlockType 1 1 2 i) (b a)) p = b.repr (b a) p.down.val
      rw [hp]
      have he : pa = p ↔ a = p.down.val := by
        constructor
        · intro h; exact congrArg (fun t : CanonicalCoord q i ↦ t.down.val) h
        · intro h; apply ULift.ext; apply Subtype.ext; exact h
      simp only [Basis.repr_self, Finsupp.single_apply, he]
    · have hz := G.blockProj_apply_mem_ne i (cwSquareBlockType 1 1 2 i)
        (cwSquarePairGrade q a) (Ne.symm ha) (b a) hmem
      have hne : a ≠ p.down.val := by
        intro h
        exact ha (h ▸ p.down.property)
      change (canonicalBasis K q i).repr
        (G.blockProj i (cwSquareBlockType 1 1 2 i) (b a)) p = b.repr (b a) p.down.val
      rw [hz]
      erw [(canonicalBasis K q i).repr.map_zero]
      simp only [Finsupp.zero_apply, Basis.repr_self,
        Finsupp.single_apply, if_neg hne]
  exact LinearMap.congr_fun hm x

/-- Canonical constituent projection preserves each coefficient in its selected coarse class. -/
theorem canonical_square_coefficient (K : Type u) [Field K] (q : ℕ)
    (p : ∀ i, CanonicalCoord.{u} q i) :
    (Basis.piTensorProduct (canonicalBasis K q)).repr (canonicalObj K q).t p =
      (Basis.piTensorProduct (cwSquareCanonicalBasis K q)).repr
        ((CWObj K q).kron (CWObj K q)).t (fun i ↦ (p i).down.val) := by
  have h (x : PiTensorProduct K ((CWObj K q).kron (CWObj K q)).V) :
      (Basis.piTensorProduct (canonicalBasis K q)).repr
        (PiTensorProduct.map (fun i ↦ (cwSquareCanonicalGrading K q).blockProj i
          (cwSquareBlockType 1 1 2 i)) x) p =
      (Basis.piTensorProduct (cwSquareCanonicalBasis K q)).repr x
        (fun i ↦ (p i).down.val) := by
    dsimp only [canonicalObj, TensorObj.TypeGrading.blockSubtensor] at *
    induction x using PiTensorProduct.induction_on with
    | smul_tprod a v =>
      rw [map_smul]
      erw [(Basis.piTensorProduct (canonicalBasis K q)).repr.map_smul]
      simp only [map_smul, map_tprod, Basis.piTensorProduct_repr_tprod_apply,
        Finsupp.smul_apply]
      apply congrArg (fun z : K ↦ a • z)
      erw [Basis.piTensorProduct_repr_tprod_apply]
      exact Finset.prod_congr rfl (fun i _ ↦ canonical_projection_coord K q i (p i) (v i))
    | add x y hx hy =>
      rw [map_add]
      erw [(Basis.piTensorProduct (canonicalBasis K q)).repr.map_add]
      simp only [map_add, Finsupp.add_apply]
      exact congrArg₂ (fun x y : K ↦ x + y) hx hy
  exact h _

end MME.CompleteSplit112


open MME MME.TensorObj MME.DWZComponentRestriction Module PiTensorProduct TensorProduct
set_option autoImplicit false

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
    {ι : Fin d → Type v} {κ : Fin d → Type w}
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
    {ι : Fin d → Type v} {κ : Fin d → Type w}
    (b : ∀ i, Basis (ι i) K (V i))
    (e : ∀ i, ι i ≃ κ i) :
    Basis.piTensorProduct (fun i ↦ (b i).reindex (e i)) =
      (Basis.piTensorProduct b).reindex (Equiv.piCongrRight e) := by
  ext w
  simp [Basis.piTensorProduct_apply,
    Module.Basis.reindex_apply]

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


/-- Recursive-word coordinates factor into the coefficients of their individual factors. -/
theorem recursive_power_coefficient
    {K : Type u} [Field K] (T : TensorObj K 3)
    {I : Fin 3 → Type u} (b : ∀ i, Basis (I i) K (T.V i))
    (n : ℕ) (w : ∀ i, PowIndex (I i) n) :
    (Basis.piTensorProduct (fun i ↦ kronPowModeBasis T i (b i) n)).repr
      (T.kronPow n).t w =
    ∏ r : Fin n, (Basis.piTensorProduct b).repr T.t
      (fun i ↦ PowIndex.get n (w i) r) := by
  induction n with
  | zero =>
    change (Basis.piTensorProduct (fun i ↦ Basis.singleton (PowIndex (I i) 0) K)).repr
      (PiTensorProduct.tprod K (fun _ ↦ (1 : K))) w = 1
    rw [Basis.piTensorProduct_repr_tprod_apply]
    simp only [Basis.singleton_repr, Finset.prod_const_one]
  | succ n ih =>
    change (Basis.piTensorProduct (fun i ↦ Basis.tensorProduct (b i)
      (kronPowModeBasis T i (b i) n))).repr (interchange T.t (T.kronPow n).t) w = _
    have h := interchange_basis_repr_explicit b
      (fun i ↦ kronPowModeBasis T i (b i) n) T.t (T.kronPow n).t
      (fun i ↦ (w i).1) (fun i ↦ (w i).2)
    have hw : (fun i ↦ ((w i).1, (w i).2)) = w := by
      funext i
      exact Prod.eta (w i)
    rw [hw] at h
    rw [h, ih, Fin.prod_univ_succ]
    rfl



open MME MME.TensorObj Module PiTensorProduct
open scoped Classical
set_option autoImplicit false

private theorem projection_on_basis
    {K : Type u} [Field K] (T : TensorObj K 3) {ι : Fin 3 → Type u}
    (b : (i : Fin 3) → Basis (ι i) K (T.V i))
    (allowed : (i : Fin 3) → ι i → Prop) (i : Fin 3) (j : ι i) :
    let G := T.basisAllAllowedGrading b allowed
    (G.classOf i 0).subtype (G.blockProj i 0 (b i j)) =
      if allowed i j then b i j else 0 := by
  classical
  dsimp only
  let G := T.basisAllAllowedGrading b allowed
  by_cases hj : allowed i j
  · rw [if_pos hj]
    have hx : b i j ∈ G.classOf i 0 := by
      change b i j ∈ cwBasisGrade (b i)
        (fun k ↦ if allowed i k then (0 : Fin 2) else 1) 0
      exact Submodule.subset_span
        ⟨j, by simp only [Set.mem_setOf_eq, if_pos hj], rfl⟩
    change (((G.modeLequiv i).symm (b i j)) 0 : T.V i) = b i j
    exact congrArg Subtype.val
      ((G.is_internal i).ofBijective_coeLinearMap_of_mem hx)
  · rw [if_neg hj]
    have hx : b i j ∈ G.classOf i 1 := by
      change b i j ∈ cwBasisGrade (b i)
        (fun k ↦ if allowed i k then (0 : Fin 2) else 1) 1
      exact Submodule.subset_span
        ⟨j, by simp only [Set.mem_setOf_eq, if_neg hj], rfl⟩
    change (((G.modeLequiv i).symm (b i j)) 0 : T.V i) = 0
    exact congrArg Subtype.val
      ((G.is_internal i).ofBijective_coeLinearMap_of_mem_ne
        (show (1 : Fin 2) ≠ 0 by decide) hx)

/-- Coordinate selection descends through source and target profile filters. -/
theorem mme_filtered_tensor_restrict_of_selected_coefficients
    {K : Type u} [Field K] (T S : TensorObj K 3)
    {I J : Fin 3 → Type u} [∀ i, Fintype (J i)]
    (b : ∀ i, Basis (I i) K (T.V i)) (c : ∀ i, Basis (J i) K (S.V i))
    (P : ∀ i, I i → Prop) (Q : ∀ i, J i → Prop) (e : ∀ i, J i → I i)
    (he : ∀ i j, Q i j → P i (e i j))
    (hc : ∀ w, (Basis.piTensorProduct b).repr T.t (fun i ↦ e i (w i)) =
      (Basis.piTensorProduct c).repr S.t w) :
    Restrict (S.basisAllAllowedSubtensor c Q) (T.basisAllAllowedSubtensor b P) := by
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
  have ht : PiTensorProduct.map f T.t = S.t := by
    apply (Basis.piTensorProduct c).repr.injective
    ext w
    exact (hmap T.t w).trans (hc w)
  let G := S.basisAllAllowedGrading c Q
  apply mme_restrict_basisAllAllowedSubtensor_of_vanishes T
    (S.basisAllAllowedSubtensor c Q) b P (fun i ↦ (G.blockProj i 0).comp (f i))
  · change PiTensorProduct.map (fun i ↦ (G.blockProj i 0).comp (f i)) T.t =
      PiTensorProduct.map (fun i ↦ G.blockProj i 0) S.t
    rw [PiTensorProduct.map_comp, LinearMap.comp_apply, ht]
  · intro i x hx
    change G.blockProj i 0 (f i (b i x)) = 0
    rw [← (c i).sum_repr (f i (b i x))]
    simp only [map_sum, map_smul]
    apply Finset.sum_eq_zero
    intro j _
    by_cases hj : Q i j
    · have hne : x ≠ e i j := fun h ↦ hx (h ▸ he i j hj)
      rw [hf]
      simp [hne]
    · have hz : G.blockProj i 0 (c i j) = 0 := by
        apply Subtype.val_injective
        change (G.classOf i 0).subtype (G.blockProj i 0 (c i j)) = 0
        rw [projection_on_basis, if_neg hj]
      rw [hz, smul_zero]


namespace MME.CompleteSplit112

open MME.DWZStep1Support

private theorem canonical_square_coefficient_factors (K : Type u) [Field K] (q : ℕ)
    (p : ∀ i, CanonicalCoord.{u} q i) :
    (Basis.piTensorProduct (canonicalBasis K q)).repr (canonicalObj K q).t p =
      (Basis.piTensorProduct (cwThreeCanonicalBasis K q)).repr (CWObj K q).t
        (fun i ↦ (p i).down.val.1) *
      (Basis.piTensorProduct (cwThreeCanonicalBasis K q)).repr (CWObj K q).t
        (fun i ↦ (p i).down.val.2) := by
  rw [canonical_square_coefficient]
  have hb : cwSquareCanonicalBasis K q = fun i ↦
      Basis.tensorProduct (cwThreeCanonicalBasis K q i) (cwThreeCanonicalBasis K q i) := by
    funext i
    fin_cases i <;> rfl
  rw [hb]
  exact interchange_basis_repr_explicit _ _ _ _ _ _

private theorem lifted_cw_coefficient (K : Type u) [Field K] (q : ℕ)
    (a : Fin 3 → ULift.{u} (Fin (q + 2))) :
    (Basis.piTensorProduct (fun i ↦ (cwThreeCanonicalBasis K q i).reindex
      Equiv.ulift.symm)).repr (CWObj K q).t a =
    (Basis.piTensorProduct (cwThreeCanonicalBasis K q)).repr (CWObj K q).t
      (fun i ↦ (a i).down) := by
  rw [piTensorProduct_basis_reindex_explicit, Basis.repr_reindex_apply]
  rfl

/-- Flattened elementary coordinates and recursive canonical coordinates have
identical tensor-power coefficients. -/
theorem canonical_intact_power_coefficient (K : Type u) [Field K] (q N : ℕ)
    (w : ∀ i, PowIndex (CanonicalCoord.{u} q i) N) :
    (Basis.piTensorProduct (CWCells.basis K q 2 N)).repr (CWCells.source K q 2 N).t
      (fun i ↦ flattenCoordinate (w i)) =
    (Basis.piTensorProduct (fun i ↦ kronPowModeBasis (canonicalObj K q) i
      (canonicalBasis K q i) N)).repr ((canonicalObj K q).kronPow N).t w := by
  rw [recursive_power_coefficient]
  change (kronPowTensorWordBasisExplicit (CWObj K q)
    (fun i ↦ (cwThreeCanonicalBasis K q i).reindex Equiv.ulift.symm) (N * 2)).repr
      ((CWObj K q).kronPow (N * 2)).t (fun i ↦ flattenCoordinate (w i)) = _
  rw [kronPowTensorWordBasis_repr_explicit]
  let f : Fin (N * 2) → K := fun r ↦
    (Basis.piTensorProduct (fun i ↦ (cwThreeCanonicalBasis K q i).reindex
      Equiv.ulift.symm)).repr (CWObj K q).t (fun i ↦ flattenCoordinate (w i) r)
  change (∏ r, f r) = _
  rw [← (finProdFinEquiv : Fin N × Fin 2 ≃ Fin (N * 2)).prod_comp f]
  rw [Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro r _
  rw [canonical_square_coefficient_factors]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one]
  simp only [f, flattenCoordinate, Equiv.symm_apply_apply,
    lifted_cw_coefficient, Matrix.cons_val_zero, Matrix.cons_val_succ]

end MME.CompleteSplit112

/-- Exact canonical 112 profile powers restrict from the literal intact CW block. -/
theorem solution
    (K : Type u) [Field K] (q N : ℕ) (beta : Fin 3 → CompleteSplit.Profile 2)
    (mu : Fin 3 → CompleteSplit.CompleteWord 2 → ℕ)
    (hmu : ∀ i sigma, (mu i sigma : ℝ) = (N : ℝ) * (beta i).probability sigma) :
    TensorObj.Restrict (CompleteSplit112.restrictedCanonicalPower K q beta 0 N)
      (RecursiveYZ.CWCells.unbroken K q 2 N (Equiv.refl _) (fun _ ↦ Unit.unit)
        (fun _ ↦ ![1, 1, 2]) (fun i _ ↦ mu i)) := by
  apply mme_filtered_tensor_restrict_of_selected_coefficients
    (RecursiveYZ.CWCells.source K q 2 N) ((CompleteSplit112.canonicalObj K q).kronPow N)
    (RecursiveYZ.CWCells.basis K q 2 N)
    (fun i ↦ DWZComponentRestriction.kronPowModeBasis (CompleteSplit112.canonicalObj K q)
      i (CompleteSplit112.canonicalBasis K q i) N)
    _ _ (fun _ ↦ CompleteSplit112.flattenCoordinate)
  · intro i w hw
    have h := (CompleteSplit112.flattenCoordinate_allowed_iff
      (beta i) (mu i) (hmu i) w).mpr hw
    fin_cases i <;> exact h
  · intro w
    exact CompleteSplit112.canonical_intact_power_coefficient K q N w



#print axioms solution
