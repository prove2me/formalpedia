-- Prove2me | solution 1 for mme_paired_oriented_matrix_power_word_basis_maps
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T03:36:11.560546+00:00
-- url     : https://prove2.me/submissions/0336cedc-d45a-4f4d-a7eb-0363cf9c76b9

import Theorems.Thm_mme_MMObj_power_third_word_basis_maps
import Definitions.Def_mme_permutation
import Definitions.Def_mme_kron_pow_word_reindex
import Definitions.Def_mme_kronPow_position_permutation_linear_data
import Definitions.Def_mme_TypeGrading_kron

open MME MME.DWZComponentRestriction PiTensorProduct Module TensorProduct BigOperators
universe u
set_option autoImplicit false

/-- Cyclic orientation preserves the numerical basis in the third mode. -/
theorem mme_MMObj_cyclic_third_basis_maps
    {K : Type u} [Field K] (n m p : ℕ) :
    ∃ f : ∀ i, (TensorObj.permObj cyclicPerm (MMObj K n m p)).V i →ₗ[K]
        (MMObj K p n m).V i,
      PiTensorProduct.map f (TensorObj.permObj cyclicPerm (MMObj K n m p)).t =
        (MMObj K p n m).t ∧
      ∀ x : Fin m × Fin p → K, f 2 x = x := by
  -- After reindexing by cyclicPerm.symm, mode i of the result is mode (cyclicPerm.symm i):
  --   mode 0 ← MMSpace n m p 2 = Fin p × Fin n → K   →  MMObj p n m mode 0 = Fin p × Fin n → K
  --   mode 1 ← MMSpace n m p 0 = Fin n × Fin m → K   →  MMObj p n m mode 1 = Fin n × Fin m → K
  --   mode 2 ← MMSpace n m p 1 = Fin m × Fin p → K   →  MMObj p n m mode 2 = Fin m × Fin p → K
  -- so each mode space matches exactly; the bijection is the identity.
  let fwd : ∀ s : Fin 3,
      (TensorObj.permObj cyclicPerm (MMObj K n m p)).V s →ₗ[K]
      (MMObj K p n m).V s := fun ⟨s, hs⟩ => by
    match s, hs with
    | 0, _ => change (Fin p × Fin n → K) →ₗ[K] (Fin p × Fin n → K); exact LinearMap.id
    | 1, _ => change (Fin n × Fin m → K) →ₗ[K] (Fin n × Fin m → K); exact LinearMap.id
    | 2, _ => change (Fin m × Fin p → K) →ₗ[K] (Fin m × Fin p → K); exact LinearMap.id
    | s + 3, h => exact absurd h (by omega)
  let bwd : ∀ s : Fin 3,
      (MMObj K p n m).V s →ₗ[K]
      (TensorObj.permObj cyclicPerm (MMObj K n m p)).V s := fun ⟨s, hs⟩ => by
    match s, hs with
    | 0, _ => change (Fin p × Fin n → K) →ₗ[K] (Fin p × Fin n → K); exact LinearMap.id
    | 1, _ => change (Fin n × Fin m → K) →ₗ[K] (Fin n × Fin m → K); exact LinearMap.id
    | 2, _ => change (Fin m × Fin p → K) →ₗ[K] (Fin m × Fin p → K); exact LinearMap.id
    | s + 3, h => exact absurd h (by omega)
  -- `fwd` and `bwd` are mutually inverse componentwise (each is `LinearMap.id` at defeq types).
  have hcomp : (fun s => fwd s ∘ₗ bwd s) = fun s => (LinearMap.id : (MMObj K p n m).V s →ₗ[K] _) := by
    funext ⟨s, hs⟩
    match s, hs with
    | 0, _ => rfl
    | 1, _ => rfl
    | 2, _ => rfl
    | s + 3, h => exact absurd h (by omega)
  -- The clean direction: `map bwd` applied to the *concrete* `MMTensor p n m` distributes fine.
  have hbwd_t : PiTensorProduct.map bwd (MMTensor K p n m) =
      (TensorObj.permObj cyclicPerm (MMObj K n m p)).t := by
    show PiTensorProduct.map bwd (MMTensor K p n m) =
        (PiTensorProduct.reindex K (MMSpace K n m p) cyclicPerm) (MMTensor K n m p)
    show PiTensorProduct.map bwd
        (∑ i : Fin p, ∑ j : Fin n, ∑ k : Fin m,
          tprod K (fun s => match s with
            | ⟨0, _⟩ => (Pi.single (i, j) 1 : Fin p × Fin n → K)
            | ⟨1, _⟩ => (Pi.single (j, k) 1 : Fin n × Fin m → K)
            | ⟨2, _⟩ => (Pi.single (k, i) 1 : Fin m × Fin p → K))) =
        (PiTensorProduct.reindex K (MMSpace K n m p) cyclicPerm)
          (∑ i : Fin n, ∑ j : Fin m, ∑ k : Fin p,
            tprod K (fun s => match s with
              | ⟨0, _⟩ => (Pi.single (i, j) 1 : Fin n × Fin m → K)
              | ⟨1, _⟩ => (Pi.single (j, k) 1 : Fin m × Fin p → K)
              | ⟨2, _⟩ => (Pi.single (k, i) 1 : Fin p × Fin n → K)))
    simp only [map_sum, PiTensorProduct.map_tprod, PiTensorProduct.reindex_tprod]
    -- LHS sums over (I:Fin p, J:Fin n, K':Fin m); RHS over (i:Fin n, j:Fin m, k:Fin p).
    -- Match: I plays k, J plays i, K' plays j. Reorder LHS to (J, K', I) = (i, j, k).
    conv_lhs => rw [Finset.sum_comm]
    conv_lhs => enter [2, J]; rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro k _
    congr 1
    ext ⟨s, hs⟩
    match s, hs with
    | 0, _ => rfl
    | 1, _ => rfl
    | 2, _ => rfl
    | s + 3, h => exact absurd h (by omega)
  -- The other direction: `map fwd` of the permuted element equals `MMTensor p n m`, derived
  -- from `hbwd_t` by composing with `bwd` (avoids distributing `map fwd` over a reindex-sum).
  have hfwd : PiTensorProduct.map fwd (TensorObj.permObj cyclicPerm (MMObj K n m p)).t =
      (MMObj K p n m).t := by
    rw [← hbwd_t, ← LinearMap.comp_apply, ← PiTensorProduct.map_comp, hcomp,
        PiTensorProduct.map_id, LinearMap.id_coe, id_eq]
    rfl
  exact ⟨fwd, hfwd, fun _ ↦ rfl⟩

/-- The other cyclic orientation also preserves the numerical third-mode basis. -/
theorem mme_MMObj_cyclic_square_third_basis_maps
    {K : Type u} [Field K] (n m p : ℕ) :
    ∃ f : ∀ i,
        (TensorObj.permObj (cyclicPerm.trans cyclicPerm) (MMObj K n m p)).V i →ₗ[K]
          (MMObj K m p n).V i,
      PiTensorProduct.map f
          (TensorObj.permObj (cyclicPerm.trans cyclicPerm) (MMObj K n m p)).t =
        (MMObj K m p n).t ∧
      ∀ x : Fin n × Fin m → K, f 2 x = x := by
  let fwd : ∀ i,
      (TensorObj.permObj (cyclicPerm.trans cyclicPerm) (MMObj K n m p)).V i →ₗ[K]
        (MMObj K m p n).V i
    | ⟨0, _⟩ => LinearMap.id
    | ⟨1, _⟩ => LinearMap.id
    | ⟨2, _⟩ => LinearMap.id
  let bwd : ∀ i, (MMObj K m p n).V i →ₗ[K]
      (TensorObj.permObj (cyclicPerm.trans cyclicPerm) (MMObj K n m p)).V i
    | ⟨0, _⟩ => LinearMap.id
    | ⟨1, _⟩ => LinearMap.id
    | ⟨2, _⟩ => LinearMap.id
  have hcomp : (fun i ↦ (fwd i).comp (bwd i)) =
      fun i ↦ (LinearMap.id : (MMObj K m p n).V i →ₗ[K] _) := by
    funext i
    fin_cases i <;> rfl
  have hbwd : PiTensorProduct.map bwd (MMObj K m p n).t =
      (TensorObj.permObj (cyclicPerm.trans cyclicPerm) (MMObj K n m p)).t := by
    change PiTensorProduct.map bwd (MMTensor K m p n) =
      PiTensorProduct.reindex K (MMSpace K n m p)
        (cyclicPerm.trans cyclicPerm) (MMTensor K n m p)
    show PiTensorProduct.map bwd
        (∑ i : Fin m, ∑ j : Fin p, ∑ k : Fin n,
          tprod K (fun s => match s with
            | ⟨0, _⟩ => (Pi.single (i, j) 1 : Fin m × Fin p → K)
            | ⟨1, _⟩ => (Pi.single (j, k) 1 : Fin p × Fin n → K)
            | ⟨2, _⟩ => (Pi.single (k, i) 1 : Fin n × Fin m → K))) =
        (PiTensorProduct.reindex K (MMSpace K n m p) (cyclicPerm.trans cyclicPerm))
          (∑ i : Fin n, ∑ j : Fin m, ∑ k : Fin p,
            tprod K (fun s => match s with
              | ⟨0, _⟩ => (Pi.single (i, j) 1 : Fin n × Fin m → K)
              | ⟨1, _⟩ => (Pi.single (j, k) 1 : Fin m × Fin p → K)
              | ⟨2, _⟩ => (Pi.single (k, i) 1 : Fin p × Fin n → K)))
    simp only [map_sum, PiTensorProduct.map_tprod, PiTensorProduct.reindex_tprod]
    conv_lhs => enter [2, i]; rw [Finset.sum_comm]
    conv_lhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    congr 1
    funext s
    fin_cases s <;> rfl
  refine ⟨fwd, ?_, fun _ ↦ rfl⟩
  rw [← hbwd, ← LinearMap.comp_apply, ← PiTensorProduct.map_comp, hcomp,
    PiTensorProduct.map_id]
  rfl

/-- A coordinate map with a specified basis action acts letter by letter
on the recursive word basis of every tensor power. -/
theorem mme_kronPow_mode_map_word_basis
    {K : Type u} [Field K] {T S : TensorObj K 3} (i : Fin 3)
    {α β : Type u} (b : Basis α K (T.V i)) (c : Basis β K (S.V i))
    (f : T.V i →ₗ[K] S.V i) (g : α → β) (hf : ∀ a, f (b a) = c (g a))
    (N : ℕ) (w : PowIndex α N) :
    TensorObj.kronPowModeMap i f N (kronPowModeBasis T i b N w) =
      kronPowModeBasis S i c N
        (PowIndex.ofFun N (fun r ↦ g (PowIndex.get N w r))) := by
  induction N with
  | zero =>
    cases w
    rfl
  | succ N ih =>
    rcases w with ⟨a,w⟩
    change TensorProduct.map f (TensorObj.kronPowModeMap i f N)
      ((b.tensorProduct (kronPowModeBasis T i b N)) (a,w)) =
      (c.tensorProduct (kronPowModeBasis S i c N))
        (g a, PowIndex.ofFun N (fun r ↦ g (PowIndex.get N w r)))
    rw [Basis.tensorProduct_apply, Basis.tensorProduct_apply,
      TensorProduct.map_tmul, hf, ih]


private theorem power_tensor_map
    {K : Type u} [Field K] {T S : TensorObj K 3}
    (f : ∀ i, T.V i →ₗ[K] S.V i)
    (hf : PiTensorProduct.map f T.t = S.t) (N : ℕ) :
    PiTensorProduct.map (fun i ↦ TensorObj.kronPowModeMap i (f i) N)
      (T.kronPow N).t = (S.kronPow N).t := by
  induction N with
  | zero =>
    exact LinearMap.congr_fun (PiTensorProduct.map_id (R := K)) _
  | succ N ih =>
    change PiTensorProduct.map
      (fun i ↦ TensorProduct.map (f i) (TensorObj.kronPowModeMap i (f i) N))
      (MME.interchange T.t (T.kronPow N).t) =
      MME.interchange S.t (S.kronPow N).t
    rw [TensorObj.TypeGrading.kronMap_interchange, hf, ih]


private theorem power_basis_identity
    {K : Type u} [Field K] {T S : TensorObj K 3} (i : Fin 3)
    {α : Type u} (b : Basis α K (T.V i)) (c : Basis α K (S.V i))
    (f : T.V i →ₗ[K] S.V i) (hf : ∀ a, f (b a) = c a)
    (N : ℕ) (w : PowIndex α N) :
    TensorObj.kronPowModeMap i f N (kronPowModeBasis T i b N w) =
      kronPowModeBasis S i c N w := by
  simpa only [id_eq, PowIndex.ofFun_get] using
    mme_kronPow_mode_map_word_basis i b c f id hf N w

/-- Cyclic orientation commutes with taking powers without changing third-mode words. -/
theorem mme_MMObj_cyclic_power_third_basis_maps
    {K : Type u} [Field K] (n m p N : ℕ) :
    let T := TensorObj.permObj cyclicPerm (MMObj K n m p)
    let S := MMObj K p n m
    let b := (Pi.basisFun K (Fin m × Fin p)).reindex Equiv.ulift.symm
    ∃ f : ∀ i, (T.kronPow N).V i →ₗ[K] (S.kronPow N).V i,
      PiTensorProduct.map f (T.kronPow N).t = (S.kronPow N).t ∧
      ∀ w : PowIndex (ULift.{u} (Fin m × Fin p)) N,
        f 2 (kronPowModeBasis T 2 b N w) = kronPowModeBasis S 2 b N w := by
  dsimp only
  obtain ⟨f, ht, hb⟩ := mme_MMObj_cyclic_third_basis_maps (K := K) n m p
  refine ⟨fun i ↦ TensorObj.kronPowModeMap i (f i) N,
    power_tensor_map f ht N, ?_⟩
  intro w
  exact power_basis_identity 2 _ _ (f 2) (fun a ↦ hb _) N w

/-- The reverse cyclic orientation commutes with powers and preserves third-mode words. -/
theorem mme_MMObj_cyclic_square_power_third_basis_maps
    {K : Type u} [Field K] (n m p N : ℕ) :
    let T := TensorObj.permObj (cyclicPerm.trans cyclicPerm) (MMObj K n m p)
    let S := MMObj K m p n
    let b := (Pi.basisFun K (Fin n × Fin m)).reindex Equiv.ulift.symm
    ∃ f : ∀ i, (T.kronPow N).V i →ₗ[K] (S.kronPow N).V i,
      PiTensorProduct.map f (T.kronPow N).t = (S.kronPow N).t ∧
      ∀ w : PowIndex (ULift.{u} (Fin n × Fin m)) N,
        f 2 (kronPowModeBasis T 2 b N w) = kronPowModeBasis S 2 b N w := by
  dsimp only
  obtain ⟨f, ht, hb⟩ := mme_MMObj_cyclic_square_third_basis_maps (K := K) n m p
  refine ⟨fun i ↦ TensorObj.kronPowModeMap i (f i) N,
    power_tensor_map f ht N, ?_⟩
  intro w
  exact power_basis_identity 2 _ _ (f 2) (fun a ↦ hb _) N w

namespace MME.PairedMatrixWordFlatten

variable {K : Type u} [Field K]

/-! ## The MM pure tensor and the unfolded `MMObj.t` (local copies) -/

/-- The pure tensor `e_{ij} ⊗ e_{jk} ⊗ e_{ki}` for indices `(i,j,k)`. -/
private noncomputable def MMPure (K : Type u) [Field K] (n m p : ℕ)
    (i : Fin n) (j : Fin m) (k : Fin p) :
    PiTensorProduct K (MMSpace K n m p) :=
  tprod K (fun (s : Fin 3) =>
    match s with
    | ⟨0, _⟩ => (Pi.single (i, j) 1 : Fin n × Fin m → K)
    | ⟨1, _⟩ => (Pi.single (j, k) 1 : Fin m × Fin p → K)
    | ⟨2, _⟩ => (Pi.single (k, i) 1 : Fin p × Fin n → K))

private theorem MMObj_t_eq (n m p : ℕ) :
    (MMObj K n m p).t = ∑ i : Fin n, ∑ j : Fin m, ∑ k : Fin p, MMPure K n m p i j k := rfl

/-! ## The mode-wise interchange on pure tensors -/

/-- `interchange` on pure tensors (local copy; the version in `Def_mme_tensor_quotient` is
private there). -/
private theorem interchange_tprod' {ι : Type*} [Fintype ι] [DecidableEq ι]
    {V W : ι → Type u} [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (v : ∀ i, V i) (w : ∀ i, W i) :
    interchange (tprod K v) (tprod K w) = tprod K (fun i => v i ⊗ₜ[K] w i) := by
  show (interchange (tprod K v)) (tprod K w) = _
  unfold interchange
  rw [PiTensorProduct.lift.tprod]
  show (PiTensorProduct.lift (interchangeInner v)) (tprod K w) = _
  rw [PiTensorProduct.lift.tprod]
  rfl

/-! ## Kronecker mode equivalence -/

/-- Curry/uncurry for function types on product domains. -/
private def uncurryEquiv (α β γ : Type*) [AddCommGroup γ] [Module K γ] :
    (α → β → γ) ≃ₗ[K] (α × β → γ) where
  toFun f p := f p.1 p.2
  map_add' _ _ := by funext ⟨_, _⟩; rfl
  map_smul' _ _ := by funext ⟨_, _⟩; rfl
  invFun f a b := f (a, b)
  left_inv _ := by funext _ _; rfl
  right_inv _ := by funext ⟨_, _⟩; rfl

/-- Kronecker mode equiv
`(Fin a × Fin b → K) ⊗ (Fin c × Fin d → K) ≃ (Fin (a*c) × Fin (b*d) → K)`
(port of Prism `kronEquiv`). -/
private noncomputable def kronEquiv (a b c d : ℕ) :
    ((Fin a × Fin b → K) ⊗[K] (Fin c × Fin d → K)) ≃ₗ[K]
      (Fin (a * c) × Fin (b * d) → K) :=
  let e2 : ((Fin a × Fin b → K) ⊗[K] (Fin c × Fin d → K)) ≃ₗ[K]
      (Fin c × Fin d → (Fin a × Fin b → K)) :=
    TensorProduct.piScalarRight K K (Fin a × Fin b → K) (Fin c × Fin d)
  let e3 : (Fin c × Fin d → (Fin a × Fin b → K)) ≃ₗ[K]
      ((Fin c × Fin d) × (Fin a × Fin b) → K) :=
    uncurryEquiv (K := K) (Fin c × Fin d) (Fin a × Fin b) K
  let reindex : (Fin a × Fin c) × (Fin b × Fin d) ≃ (Fin c × Fin d) × (Fin a × Fin b) :=
    (Equiv.prodProdProdComm (Fin a) (Fin c) (Fin b) (Fin d)).trans (Equiv.prodComm _ _)
  let e4 : ((Fin c × Fin d) × (Fin a × Fin b) → K) ≃ₗ[K]
      ((Fin a × Fin c) × (Fin b × Fin d) → K) :=
    LinearEquiv.funCongrLeft K K reindex
  let e5 : ((Fin a × Fin c) × (Fin b × Fin d) → K) ≃ₗ[K]
      (Fin (a * c) × Fin (b * d) → K) :=
    LinearEquiv.funCongrLeft K K
      (Equiv.prodCongr finProdFinEquiv.symm finProdFinEquiv.symm)
  e2.trans (e3.trans (e4.trans e5))

/-- Action of `kronEquiv` on a pure tensor of basis elements (port of Prism
`kronEquiv_single`). -/
private theorem kronEquiv_single {a b c d : ℕ}
    (i : Fin a) (j : Fin b) (i' : Fin c) (j' : Fin d) :
    kronEquiv (K := K) a b c d ((Pi.single (i, j) 1) ⊗ₜ[K] (Pi.single (i', j') 1)) =
      Pi.single (finProdFinEquiv (i, i'), finProdFinEquiv (j, j')) 1 := by
  funext IJ; obtain ⟨I, J⟩ := IJ
  have lhs_val :
      ((kronEquiv (K := K) a b c d)
          ((Pi.single (i, j) 1) ⊗ₜ[K] (Pi.single (i', j') 1))) (I, J) =
        ((Pi.single (i', j') 1 : Fin c × Fin d → K)
            ((finProdFinEquiv.symm I).2, (finProdFinEquiv.symm J).2)) *
          ((Pi.single (i, j) 1 : Fin a × Fin b → K)
            ((finProdFinEquiv.symm I).1, (finProdFinEquiv.symm J).1)) := by
    simp only [kronEquiv, uncurryEquiv, LinearEquiv.trans_apply, LinearEquiv.coe_mk,
      LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply,
      TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul,
      Equiv.prodCongr_apply, Prod.map_apply, Equiv.trans_apply,
      Equiv.prodProdProdComm_apply, Equiv.prodComm_apply, Prod.swap]
    rfl
  rw [lhs_val]
  simp only [Pi.single_apply, Prod.mk.injEq]
  set I' : Fin a × Fin c := finProdFinEquiv.symm I with hIdef
  set J' : Fin b × Fin d := finProdFinEquiv.symm J with hJdef
  have hIeq : I = finProdFinEquiv I' := by
    rw [hIdef]; exact (finProdFinEquiv.apply_symm_apply I).symm
  have hJeq : J = finProdFinEquiv J' := by
    rw [hJdef]; exact (finProdFinEquiv.apply_symm_apply J).symm
  rw [hIeq, hJeq]
  simp only [finProdFinEquiv.injective.eq_iff]
  obtain ⟨I'1, I'2⟩ := I'
  obtain ⟨J'1, J'2⟩ := J'
  by_cases hI2 : I'2 = i'
  · by_cases hJ2 : J'2 = j'
    · by_cases hI1 : I'1 = i
      · by_cases hJ1 : J'1 = j
        · simp [hI1, hI2, hJ1, hJ2]
        · simp [hI1, hI2, hJ1, hJ2]
      · simp [hI1, hI2, hJ2]
    · simp [hJ2, hI2]
  · simp [hI2]

/-! ## The mode-wise equivalence family and its per-term action -/

/-- The per-mode linear equivalences realizing `MM(n,m,p) ⊗ MM(n',m',p') ≅ MM(nn',mm',pp')`.
Mode `0` glues the `(Fin n × Fin m)`/`(Fin n' × Fin m')` indices, etc. -/
private noncomputable def modeEquiv (n m p n' m' p' : ℕ) : ∀ i : Fin 3,
    (TensorObj.kron (MMObj K n m p) (MMObj K n' m' p')).V i ≃ₗ[K]
      (MMObj K (n * n') (m * m') (p * p')).V i
  | ⟨0, _⟩ => kronEquiv n m n' m'
  | ⟨1, _⟩ => kronEquiv m p m' p'
  | ⟨2, _⟩ => kronEquiv p n p' n'
  | ⟨s + 3, h⟩ => absurd h (by omega)

/-- The induced `PiTensorProduct.map` sends each `interchange`d pair of basis pure tensors
to the corresponding basis pure tensor on the product object. -/
private theorem modeEquiv_pure (n m p n' m' p' : ℕ)
    (i : Fin n) (j : Fin m) (k : Fin p) (i' : Fin n') (j' : Fin m') (k' : Fin p') :
    PiTensorProduct.map (fun s => (modeEquiv (K := K) n m p n' m' p' s).toLinearMap)
        (interchange (MMPure K n m p i j k) (MMPure K n' m' p' i' j' k')) =
      MMPure K (n * n') (m * m') (p * p')
        (finProdFinEquiv (i, i')) (finProdFinEquiv (j, j')) (finProdFinEquiv (k, k')) := by
  -- The `interchange` of the two basis pure tensors is itself a pure tensor.
  have hint :
      interchange (MMPure K n m p i j k) (MMPure K n' m' p' i' j' k') =
        tprod K (fun s : Fin 3 =>
          (match s with
            | ⟨0, _⟩ => (Pi.single (i, j) 1 : Fin n × Fin m → K)
            | ⟨1, _⟩ => (Pi.single (j, k) 1 : Fin m × Fin p → K)
            | ⟨2, _⟩ => (Pi.single (k, i) 1 : Fin p × Fin n → K) :
              MMSpace K n m p s) ⊗ₜ[K]
          (match s with
            | ⟨0, _⟩ => (Pi.single (i', j') 1 : Fin n' × Fin m' → K)
            | ⟨1, _⟩ => (Pi.single (j', k') 1 : Fin m' × Fin p' → K)
            | ⟨2, _⟩ => (Pi.single (k', i') 1 : Fin p' × Fin n' → K) :
              MMSpace K n' m' p' s)) :=
    interchange_tprod'
      (V := MMSpace K n m p) (W := MMSpace K n' m' p')
      (fun s => match s with
        | ⟨0, _⟩ => (Pi.single (i, j) 1 : Fin n × Fin m → K)
        | ⟨1, _⟩ => (Pi.single (j, k) 1 : Fin m × Fin p → K)
        | ⟨2, _⟩ => (Pi.single (k, i) 1 : Fin p × Fin n → K))
      (fun s => match s with
        | ⟨0, _⟩ => (Pi.single (i', j') 1 : Fin n' × Fin m' → K)
        | ⟨1, _⟩ => (Pi.single (j', k') 1 : Fin m' × Fin p' → K)
        | ⟨2, _⟩ => (Pi.single (k', i') 1 : Fin p' × Fin n' → K))
  -- Apply `map equiv` to both sides of `hint`, then compute on the resulting pure tensor.
  refine (congrArg (PiTensorProduct.map (fun s => (modeEquiv (K := K) n m p n' m' p' s).toLinearMap)) hint).trans ?_
  erw [PiTensorProduct.map_tprod]
  show PiTensorProduct.tprod K _ = MMPure K (n * n') (m * m') (p * p') _ _ _
  simp only [MMPure]
  congr 1
  funext s
  fin_cases s
  · exact kronEquiv_single (K := K) i j i' j'
  · exact kronEquiv_single (K := K) j k j' k'
  · exact kronEquiv_single (K := K) k i k' i'

/-! ## The forward restriction `kron MM MM ← MM(nn',mm',pp')` (via the equivalences) -/

/-- The mode equivalences carry `(kron MM MM).t` to `MM(nn',mm',pp').t`.  This is the
genuine content: distributing `map ∘ interchange` over the two triple sums and reindexing
the resulting six-fold sum by `finProdFinEquiv` on each mode. -/
private theorem map_modeEquiv_kron_t (n m p n' m' p' : ℕ) :
    PiTensorProduct.map (fun s => (modeEquiv (K := K) n m p n' m' p' s).toLinearMap)
        (TensorObj.kron (MMObj K n m p) (MMObj K n' m' p')).t =
      (MMObj K (n * n') (m * m') (p * p')).t := by
  show PiTensorProduct.map (fun s => (modeEquiv (K := K) n m p n' m' p' s).toLinearMap)
      (interchange (MMObj K n m p).t (MMObj K n' m' p').t) =
      (MMObj K (n * n') (m * m') (p * p')).t
  rw [MMObj_t_eq, MMObj_t_eq, MMObj_t_eq]
  -- Push the interchange-sums out (it is bilinear): `map_sum₂` for the left argument,
  -- `map_sum` for the right argument and the outer `PiTensorProduct.map`.
  have hdist :
      interchange (K := K) (∑ i, ∑ j, ∑ k, MMPure K n m p i j k)
          (∑ i', ∑ j', ∑ k', MMPure K n' m' p' i' j' k') =
        ∑ i, ∑ j, ∑ k, ∑ i', ∑ j', ∑ k',
          interchange (K := K) (MMPure K n m p i j k) (MMPure K n' m' p' i' j' k') := by
    rw [LinearMap.map_sum₂]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.map_sum₂]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [LinearMap.map_sum₂]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun i' _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun j' _ => ?_
    rw [map_sum]
  -- Apply `map equiv` to both sides of `hdist`, push it through the six sums, and apply
  -- `modeEquiv_pure` on each pure term.  This rewrites the LHS to the six-fold sum of
  -- target pure tensors `MMPure (nn',mm',pp') (i,i')* (j,j')* (k,k')*`.
  refine (congrArg (PiTensorProduct.map
    (fun s => (modeEquiv (K := K) n m p n' m' p' s).toLinearMap)) hdist).trans ?_
  refine
    (show (PiTensorProduct.map (fun s => (modeEquiv (K := K) n m p n' m' p' s).toLinearMap))
        (∑ i, ∑ j, ∑ k, ∑ i', ∑ j', ∑ k',
          interchange (K := K) (MMPure K n m p i j k) (MMPure K n' m' p' i' j' k')) =
      ∑ i, ∑ j, ∑ k, ∑ i', ∑ j', ∑ k',
        MMPure K (n * n') (m * m') (p * p')
          (finProdFinEquiv (i, i')) (finProdFinEquiv (j, j')) (finProdFinEquiv (k, k'))
      from by
        refine (map_sum _ _ _).trans (Finset.sum_congr rfl fun i _ => ?_)
        refine (map_sum _ _ _).trans (Finset.sum_congr rfl fun j _ => ?_)
        refine (map_sum _ _ _).trans (Finset.sum_congr rfl fun k _ => ?_)
        refine (map_sum _ _ _).trans (Finset.sum_congr rfl fun i' _ => ?_)
        refine (map_sum _ _ _).trans (Finset.sum_congr rfl fun j' _ => ?_)
        refine (map_sum _ _ _).trans (Finset.sum_congr rfl fun k' _ => ?_)
        exact modeEquiv_pure n m p n' m' p' i j k i' j' k').trans ?_
  -- Reorder the LHS sums from `(i,j,k,i',j',k')` to `(i,i',j,j',k,k')`.
  have hLHS :
      (∑ i : Fin n, ∑ j : Fin m, ∑ k : Fin p, ∑ i' : Fin n', ∑ j' : Fin m', ∑ k' : Fin p',
          MMPure K (n * n') (m * m') (p * p')
            (finProdFinEquiv (i, i')) (finProdFinEquiv (j, j')) (finProdFinEquiv (k, k'))) =
      (∑ i : Fin n, ∑ i' : Fin n', ∑ j : Fin m, ∑ j' : Fin m', ∑ k : Fin p, ∑ k' : Fin p',
          MMPure K (n * n') (m * m') (p * p')
            (finProdFinEquiv (i, i')) (finProdFinEquiv (j, j')) (finProdFinEquiv (k, k'))) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    -- Under fixed `i`:  ∑j∑k∑i'∑j'∑k'  =  ∑i'∑j∑j'∑k∑k'.
    -- Step 1: pull `i'` to the front (swap k,i' under j, then j,i').
    rw [show (∑ j : Fin m, ∑ k : Fin p, ∑ i' : Fin n', ∑ j' : Fin m', ∑ k' : Fin p',
          MMPure K (n * n') (m * m') (p * p')
            (finProdFinEquiv (i, i')) (finProdFinEquiv (j, j')) (finProdFinEquiv (k, k'))) =
        (∑ j : Fin m, ∑ i' : Fin n', ∑ k : Fin p, ∑ j' : Fin m', ∑ k' : Fin p',
          MMPure K (n * n') (m * m') (p * p')
            (finProdFinEquiv (i, i')) (finProdFinEquiv (j, j')) (finProdFinEquiv (k, k')))
      from Finset.sum_congr rfl fun j _ => Finset.sum_comm]   -- swap k,i' under j
    rw [Finset.sum_comm (γ := Fin n')]                          -- ∑i'∑j∑k∑j'∑k'
    refine Finset.sum_congr rfl fun i' _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    -- Step 2: under i',j:  ∑k∑j'∑k'  =  ∑j'∑k∑k'  (swap k,j').
    rw [Finset.sum_comm (γ := Fin m')]
  rw [hLHS]
  -- Reindex the RHS triple sum by `finProdFinEquiv` on each mode, then split products into
  -- the matching six-fold sum `(i,i',j,j',k,k')`.
  rw [show (∑ I : Fin (n * n'), ∑ J : Fin (m * m'), ∑ Kk : Fin (p * p'),
        MMPure K (n * n') (m * m') (p * p') I J Kk) =
      ∑ ii' : Fin n × Fin n', ∑ jj' : Fin m × Fin m', ∑ kk' : Fin p × Fin p',
        MMPure K (n * n') (m * m') (p * p')
          (finProdFinEquiv ii') (finProdFinEquiv jj') (finProdFinEquiv kk')
      from by
        rw [← finProdFinEquiv.sum_comp]
        refine Finset.sum_congr rfl fun _ _ => ?_
        rw [← finProdFinEquiv.sum_comp]
        refine Finset.sum_congr rfl fun _ _ => ?_
        rw [← finProdFinEquiv.sum_comp]]
  simp_rw [Fintype.sum_prod_type]

/-- The canonical mode-wise equivalence identifying the Kronecker product
of two matrix-multiplication spaces with the corresponding product-sized
matrix-multiplication space. -/
noncomputable def MMObjKronModeEquiv (n m p n' m' p' : ℕ) :
    ∀ i : Fin 3,
      (TensorObj.kron (MMObj K n m p) (MMObj K n' m' p')).V i ≃ₗ[K]
        (MMObj K (n * n') (m * m') (p * p')).V i :=
  modeEquiv n m p n' m' p'

/-- The canonical Kronecker mode equivalences carry the tensor element to
the product-sized matrix-multiplication tensor. -/
theorem map_MMObjKronModeEquiv_kron_t (n m p n' m' p' : ℕ) :
    PiTensorProduct.map
        (fun i ↦
          (MMObjKronModeEquiv (K := K) n m p n' m' p' i).toLinearMap)
        (TensorObj.kron (MMObj K n m p) (MMObj K n' m' p')).t =
      (MMObj K (n * n') (m * m') (p * p')).t :=
  map_modeEquiv_kron_t n m p n' m' p'


end MME.PairedMatrixWordFlatten

/-- In the shared matrix coordinate, the canonical Kronecker equivalence
concatenates the row labels and column labels separately. -/
theorem paired_kron_mode_two_single
    {K : Type u} [Field K] (n m p n' m' p' : ℕ)
    (k : Fin p) (i : Fin n) (k' : Fin p') (i' : Fin n') :
    (PairedMatrixWordFlatten.MMObjKronModeEquiv (K := K) n m p n' m' p' 2)
      ((Pi.single (k, i) 1) ⊗ₜ[K] (Pi.single (k', i') 1)) =
      Pi.single (finProdFinEquiv (k, k'), finProdFinEquiv (i, i')) 1 := by
  classical
  funext x
  rcases x with ⟨a, b⟩
  change ((Pi.single (k', i') 1 : Fin p' × Fin n' → K)
      ((finProdFinEquiv.symm a).2, (finProdFinEquiv.symm b).2)) *
    ((Pi.single (k, i) 1 : Fin p × Fin n → K)
      ((finProdFinEquiv.symm a).1, (finProdFinEquiv.symm b).1)) = _
  obtain ⟨⟨a, a'⟩, rfl⟩ := finProdFinEquiv.surjective a
  obtain ⟨⟨b, b'⟩, rfl⟩ := finProdFinEquiv.surjective b
  simp only [Equiv.symm_apply_apply, Pi.single_apply, Prod.mk.injEq,
    finProdFinEquiv.injective.eq_iff]
  split_ifs <;> simp_all


/-- Flattening the two cyclic matrix powers gives a matrix whose row and column
labels are independently equivalent to the two complete third-mode word sets. -/
private theorem paired_oriented_matrix_power_word_basis_maps_aux
    {K : Type u} [Field K] (q N : ℕ) :
    let U := TensorObj.permObj (cyclicPerm.trans cyclicPerm) (MMObj K 1 q 1)
    let V := TensorObj.permObj cyclicPerm (MMObj K 1 q 1)
    let c := (Pi.basisFun K (Fin 1 × Fin q)).reindex Equiv.ulift.symm
    let e := (Pi.basisFun K (Fin q × Fin 1)).reindex Equiv.ulift.symm
    ∃ F : ∀ i, ((U.kronPow N).kron (V.kronPow N)).V i →ₗ[K]
        (MMObj K (q^N * 1) (1 * 1) (1 * q^N)).V i,
    ∃ rows : PowIndex (ULift.{u} (Fin q × Fin 1)) N ≃ Fin (1 * q^N),
    ∃ cols : PowIndex (ULift.{u} (Fin 1 × Fin q)) N ≃ Fin (q^N * 1),
      PiTensorProduct.map F ((U.kronPow N).kron (V.kronPow N)).t =
        (MMObj K (q^N * 1) (1 * 1) (1 * q^N)).t ∧
      ∀ x y, F 2 ((kronPowModeBasis U 2 c N x) ⊗ₜ[K]
          (kronPowModeBasis V 2 e N y)) = Pi.single (rows y, cols x) 1 := by
  dsimp only
  obtain ⟨fU, hfU, hbU⟩ := mme_MMObj_cyclic_square_power_third_basis_maps
    (K := K) 1 q 1 N
  obtain ⟨fV, hfV, hbV⟩ := mme_MMObj_cyclic_power_third_basis_maps
    (K := K) 1 q 1 N
  have hu := mme_MMObj_power_third_word_basis_maps (K := K) q 1 1 N
  have hv := mme_MMObj_power_third_word_basis_maps (K := K) 1 1 q N
  dsimp only at hu hv
  rw [Nat.one_pow] at hu hv
  obtain ⟨gU, rU, cU, hgU, bgU⟩ := hu
  obtain ⟨gV, rV, cV, hgV, bgV⟩ := hv
  let rowLetter : ULift.{u} (Fin q × Fin 1) ≃ ULift.{u} (Fin q) :=
    Equiv.ulift.trans ((Equiv.prodUnique (Fin q) (Fin 1)).trans Equiv.ulift.symm)
  let colLetter : ULift.{u} (Fin 1 × Fin q) ≃ ULift.{u} (Fin q) :=
    Equiv.ulift.trans ((Equiv.uniqueProd (Fin q) (Fin 1)).trans Equiv.ulift.symm)
  let rowWords := (PowIndex.equivFun (ULift.{u} (Fin q × Fin 1)) N).trans
    ((Equiv.piCongrRight (fun _ : Fin N ↦ rowLetter)).trans
      (PowIndex.equivFun (ULift.{u} (Fin q)) N).symm)
  let colWords := (PowIndex.equivFun (ULift.{u} (Fin 1 × Fin q)) N).trans
    ((Equiv.piCongrRight (fun _ : Fin N ↦ colLetter)).trans
      (PowIndex.equivFun (ULift.{u} (Fin q)) N).symm)
  let rows := rowWords.trans (rV.trans
    ((Equiv.uniqueProd (Fin (q^N)) (Fin 1)).symm.trans finProdFinEquiv))
  let cols := colWords.trans (cU.trans
    ((Equiv.prodUnique (Fin (q^N)) (Fin 1)).symm.trans finProdFinEquiv))
  let hU := fun i ↦ (gU i).comp (fU i)
  let hV := fun i ↦ (gV i).comp (fV i)
  let F := fun i ↦
    (PairedMatrixWordFlatten.MMObjKronModeEquiv (K := K) (q^N) 1 1 1 1 (q^N) i).toLinearMap.comp
      (TensorProduct.map (hU i) (hV i))
  refine ⟨F, rows, cols, ?_, ?_⟩
  · have htu : PiTensorProduct.map hU
        ((TensorObj.permObj (cyclicPerm.trans cyclicPerm) (MMObj K 1 q 1)).kronPow N).t =
        (MMObj K (q^N) 1 1).t := by
      rw [PiTensorProduct.map_comp, LinearMap.comp_apply, hfU, hgU]
    have htv : PiTensorProduct.map hV
        ((TensorObj.permObj cyclicPerm (MMObj K 1 q 1)).kronPow N).t =
        (MMObj K 1 1 (q^N)).t := by
      rw [PiTensorProduct.map_comp, LinearMap.comp_apply, hfV, hgV]
    dsimp only [F]
    erw [PiTensorProduct.map_comp, LinearMap.comp_apply]
    change PiTensorProduct.map _ (PiTensorProduct.map _ (MME.interchange _ _)) = _
    have hi := TensorObj.TypeGrading.kronMap_interchange hU hV
      ((TensorObj.permObj (cyclicPerm.trans cyclicPerm) (MMObj K 1 q 1)).kronPow N).t
      ((TensorObj.permObj cyclicPerm (MMObj K 1 q 1)).kronPow N).t
    rw [htu, htv] at hi
    erw [hi]
    exact PairedMatrixWordFlatten.map_MMObjKronModeEquiv_kron_t (q^N) 1 1 1 1 (q^N)
  · intro x y
    dsimp only [F, hU, hV, LinearMap.comp_apply]
    erw [LinearMap.comp_apply, TensorProduct.map_tmul]
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hbU, hbV, bgU, bgV]
    erw [paired_kron_mode_two_single]
    congr 1
    apply Prod.ext
    · change finProdFinEquiv (_, _) = finProdFinEquiv (0, _)
      congr 1
      exact Prod.ext (Subsingleton.elim _ _) rfl
    · change finProdFinEquiv (_, _) = finProdFinEquiv (_, 0)
      congr 1
      exact Prod.ext rfl (Subsingleton.elim _ _)

/-- The oriented matrix powers flatten to a matrix with independent word labels. -/
theorem solution
    {K : Type u} [Field K] (q N : ℕ) :
    let U := TensorObj.permObj (cyclicPerm.trans cyclicPerm) (MMObj K 1 q 1)
    let V := TensorObj.permObj cyclicPerm (MMObj K 1 q 1)
    let c := (Pi.basisFun K (Fin 1 × Fin q)).reindex Equiv.ulift.symm
    let e := (Pi.basisFun K (Fin q × Fin 1)).reindex Equiv.ulift.symm
    ∃ F : ∀ i, ((U.kronPow N).kron (V.kronPow N)).V i →ₗ[K]
        (MMObj K (q^N) 1 (q^N)).V i,
    ∃ rows : PowIndex (ULift.{u} (Fin q × Fin 1)) N ≃ Fin (q^N),
    ∃ cols : PowIndex (ULift.{u} (Fin 1 × Fin q)) N ≃ Fin (q^N),
      PiTensorProduct.map F ((U.kronPow N).kron (V.kronPow N)).t =
        (MMObj K (q^N) 1 (q^N)).t ∧
      ∀ x y, F 2 ((kronPowModeBasis U 2 c N x) ⊗ₜ[K]
          (kronPowModeBasis V 2 e N y)) = Pi.single (rows y, cols x) 1 := by
  have h := paired_oriented_matrix_power_word_basis_maps_aux (K := K) q N
  dsimp only at h ⊢
  rw [Nat.mul_one, Nat.one_mul, Nat.one_mul] at h
  exact h

#print axioms solution
