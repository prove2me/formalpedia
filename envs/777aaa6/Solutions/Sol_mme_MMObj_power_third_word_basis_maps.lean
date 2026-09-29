-- Prove2me | solution 1 for mme_MMObj_power_third_word_basis_maps
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T03:27:18.632986+00:00
-- url     : https://prove2.me/submissions/f444afa9-6afb-4b30-8945-6587e615aa46

import Definitions.Def_mme_mmobj_mul
import Definitions.Def_mme_kron_pow_word_reindex
import Definitions.Def_mme_kronPow_position_permutation_linear_data
import Definitions.Def_mme_TypeGrading_kron
import Mathlib.Tactic.FinCases

open MME MME.DWZComponentRestriction PiTensorProduct Module TensorProduct BigOperators
universe u
set_option autoImplicit false

namespace MME.MatrixWordFlatten

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


end MME.MatrixWordFlatten

/-- In the shared matrix coordinate, the canonical Kronecker equivalence
concatenates the row labels and column labels separately. -/
theorem mme_MMObj_kron_mode_two_single
    {K : Type u} [Field K] (n m p n' m' p' : ℕ)
    (k : Fin p) (i : Fin n) (k' : Fin p') (i' : Fin n') :
    (MatrixWordFlatten.MMObjKronModeEquiv (K := K) n m p n' m' p' 2)
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

/-- Matrix powers can be flattened while retaining separate row-word and
column-word labels on the shared coordinate. -/
theorem solution
    {K : Type u} [Field K] (n m p N : ℕ) :
    let T := MMObj K n m p
    let b := (Pi.basisFun K (Fin p × Fin n)).reindex Equiv.ulift.symm
    ∃ (f : ∀ i, (T.kronPow N).V i →ₗ[K] (MMObj K (n^N) (m^N) (p^N)).V i)
      (rows : PowIndex (ULift.{u} (Fin p)) N ≃ Fin (p^N))
      (cols : PowIndex (ULift.{u} (Fin n)) N ≃ Fin (n^N)),
      PiTensorProduct.map f (T.kronPow N).t = (MMObj K (n^N) (m^N) (p^N)).t ∧
      ∀ w : PowIndex (ULift.{u} (Fin p × Fin n)) N,
        f 2 (kronPowModeBasis T 2 b N w) =
          Pi.single
            (rows (PowIndex.ofFun N (fun r ↦ ⟨(PowIndex.get N w r).down.1⟩)),
             cols (PowIndex.ofFun N (fun r ↦ ⟨(PowIndex.get N w r).down.2⟩))) 1 := by
  dsimp only
  induction N with
  | zero =>
    simp only [Nat.pow_zero]
    let f : ∀ i : Fin 3, K →ₗ[K] MMSpace K 1 1 1 i
      | ⟨0, _⟩ => LinearMap.pi (fun _ ↦ LinearMap.id)
      | ⟨1, _⟩ => LinearMap.pi (fun _ ↦ LinearMap.id)
      | ⟨2, _⟩ => LinearMap.pi (fun _ ↦ LinearMap.id)
    refine ⟨f, Equiv.ofUnique _ _, Equiv.ofUnique _ _, ?_, ?_⟩
    · change PiTensorProduct.map f (PiTensorProduct.tprod K (fun _ ↦ (1 : K))) = _
      rw [PiTensorProduct.map_tprod]
      change PiTensorProduct.tprod K _ = MMTensor K 1 1 1
      simp only [MMTensor, Fintype.sum_unique]
      congr 1
      funext i
      fin_cases i <;> funext x <;>
        simp [f, Pi.single_apply, Subsingleton.elim x (0, 0)] <;> rfl
    · intro w
      cases w
      funext x
      rcases x with ⟨a, b⟩
      fin_cases a
      fin_cases b
      change (Basis.singleton (PowIndex (ULift.{u} (Fin p × Fin n)) 0) K) PUnit.unit = _
      rw [Basis.singleton_apply]
      erw [Pi.single_apply]
      simp
      exact ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  | succ N ih =>
    obtain ⟨f, rows, cols, hf, hb⟩ := ih
    rw [Nat.pow_succ', Nat.pow_succ', Nat.pow_succ']
    let F := fun i ↦
      (MatrixWordFlatten.MMObjKronModeEquiv (K := K) n m p (n^N) (m^N) (p^N) i).toLinearMap.comp
        (TensorProduct.map LinearMap.id (f i))
    let rows' : PowIndex (ULift.{u} (Fin p)) (N+1) ≃ Fin (p * p^N) :=
      (Equiv.prodCongr Equiv.ulift rows).trans finProdFinEquiv
    let cols' : PowIndex (ULift.{u} (Fin n)) (N+1) ≃ Fin (n * n^N) :=
      (Equiv.prodCongr Equiv.ulift cols).trans finProdFinEquiv
    refine ⟨F, rows', cols', ?_, ?_⟩
    · dsimp only [F]
      erw [PiTensorProduct.map_comp, LinearMap.comp_apply]
      change PiTensorProduct.map _
        (PiTensorProduct.map _ (MME.interchange (MMObj K n m p).t
          ((MMObj K n m p).kronPow N).t)) = _
      have hmap := TensorObj.TypeGrading.kronMap_interchange
        (fun i ↦ (LinearMap.id : (MMObj K n m p).V i →ₗ[K] (MMObj K n m p).V i))
        f (MMObj K n m p).t ((MMObj K n m p).kronPow N).t
      rw [hf, PiTensorProduct.map_id] at hmap
      erw [hmap]
      exact MatrixWordFlatten.map_MMObjKronModeEquiv_kron_t n m p (n^N) (m^N) (p^N)
    · rintro ⟨a, w⟩
      dsimp only [kronPowModeBasis]
      erw [Basis.tensorProduct_apply]
      change (MatrixWordFlatten.MMObjKronModeEquiv (K := K) n m p (n^N) (m^N) (p^N) 2)
        (TensorProduct.map LinearMap.id (f 2)
          (((Pi.basisFun K (Fin p × Fin n)).reindex Equiv.ulift.symm) a ⊗ₜ[K]
            kronPowModeBasis (MMObj K n m p) 2
              ((Pi.basisFun K (Fin p × Fin n)).reindex Equiv.ulift.symm) N w)) = _
      rw [TensorProduct.map_tmul, LinearMap.id_apply, hb]
      erw [Basis.reindex_apply, Pi.basisFun_apply]
      exact mme_MMObj_kron_mode_two_single n m p (n^N) (m^N) (p^N)
        a.down.1 a.down.2 _ _

#print axioms solution
