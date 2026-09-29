-- Prove2me | solution 1 for mme_coupled_paired_trace_source_word_projection_restriction
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T03:08:32.254672+00:00
-- url     : https://prove2.me/submissions/e181d5b0-d5ab-4e64-b570-e353d4b17e58

import Definitions.Def_mme_permutation
import Definitions.Def_mme_TypeGrading_kron
import Definitions.Def_mme_CW_coupled_value
import Definitions.Def_mme_tensor_rank
import Definitions.Def_mme_kron_pow_word_reindex
import Definitions.Def_mme_kronPow_position_permutation_linear_data
import Mathlib.Tactic.FinCases

open MME MME.DWZComponentRestriction PiTensorProduct Module TensorProduct BigOperators
universe u
set_option autoImplicit false

namespace MME.CoupledTrace
variable {K : Type u} [Field K] {q : ℕ}
noncomputable def monom (x y : Fin q ⊕ Fin q) (z : Fin 2 ⊕ (Fin q × Fin q)) :
    PiTensorProduct K (CoupledSpace K q) :=
  tprod K (fun s ↦ match s with
    | ⟨0, _⟩ => Pi.single x 1
    | ⟨1, _⟩ => Pi.single y 1
    | ⟨2, _⟩ => Pi.single z 1)

noncomputable def traceEval : ((Fin 2 ⊕ (Fin q × Fin q)) → K) →ₗ[K] K :=
  ∑ i : Fin q, LinearMap.proj (Sum.inr (i, i))

noncomputable def traceMaps : ∀ s : Fin 3,
    CoupledSpace K q s →ₗ[K] MMSpace K 1 (q + q) 1 s
  | ⟨0, _⟩ => LinearMap.pi (fun p ↦ LinearMap.proj (finSumFinEquiv.symm p.2))
  | ⟨1, _⟩ => LinearMap.pi (fun p ↦ LinearMap.proj (Sum.swap (finSumFinEquiv.symm p.1)))
  | ⟨2, _⟩ => LinearMap.pi (fun _ ↦ traceEval)

private theorem trace_monom_zero (x y : Fin q ⊕ Fin q)
    (w : Fin 2 ⊕ (Fin q × Fin q)) (hw : ∀ i : Fin q, w ≠ Sum.inr (i, i)) :
    PiTensorProduct.map (traceMaps (K := K)) (monom x y w) = 0 := by
  classical
  rw [monom, PiTensorProduct.map_tprod]
  apply (PiTensorProduct.tprod K).map_coord_zero 2
  ext p
  change (traceEval (K := K) (q := q))
    (Pi.single w 1 : (Fin 2 ⊕ (Fin q × Fin q)) → K) = 0
  simp only [traceEval, LinearMap.sum_apply, LinearMap.proj_apply]
  exact Finset.sum_eq_zero (fun i _ ↦ by simp [Ne.symm (hw i)])

private theorem single_reindex (x : Fin q ⊕ Fin q) (j : Fin (q + q)) :
    (Pi.single x 1 : (Fin q ⊕ Fin q) → K) (finSumFinEquiv.symm j) =
      (Pi.single (finSumFinEquiv x) 1 : Fin (q + q) → K) j := by
  classical
  simp only [Pi.single_apply, Equiv.symm_apply_eq]

private theorem single_swap_reindex (x : Fin q ⊕ Fin q) (j : Fin (q + q)) :
    (Pi.single (Sum.swap x) 1 : (Fin q ⊕ Fin q) → K)
      (Sum.swap (finSumFinEquiv.symm j)) =
      (Pi.single (finSumFinEquiv x) 1 : Fin (q + q) → K) j := by
  classical
  have hswap : Function.Injective (@Sum.swap (Fin q) (Fin q)) := by
    intro a b h
    simpa using congrArg Sum.swap h
  simp only [Pi.single_apply, hswap.eq_iff, Equiv.symm_apply_eq]

private theorem trace_diag (i : Fin q) :
    (traceEval (K := K) (q := q))
      (Pi.single (Sum.inr (i,i)) 1 : (Fin 2 ⊕ (Fin q × Fin q)) → K) = 1 := by
  classical
  simp [traceEval, LinearMap.sum_apply, LinearMap.proj_apply, Pi.single_apply, Prod.mk.injEq]

noncomputable def mmMonom (j : Fin (q + q)) : PiTensorProduct K (MMSpace K 1 (q + q) 1) :=
  tprod K (fun s ↦ match s with
    | ⟨0, _⟩ => Pi.single (0,j) 1
    | ⟨1, _⟩ => Pi.single (j,0) 1
    | ⟨2, _⟩ => Pi.single (0,0) 1)

private theorem trace_left (i : Fin q) :
    PiTensorProduct.map (traceMaps (K := K))
      (monom (Sum.inl i) (Sum.inr i) (Sum.inr (i,i))) =
        mmMonom (finSumFinEquiv (Sum.inl i)) := by
  classical
  rw [monom, PiTensorProduct.map_tprod, mmMonom]
  congr 1
  funext s
  fin_cases s
  · ext p
    change (Pi.single (Sum.inl i) 1 : (Fin q ⊕ Fin q) → K) (finSumFinEquiv.symm p.2) = _
    rw [single_reindex]
    simp [Pi.single_apply, Prod.ext_iff, Subsingleton.elim p.1 0]
  · ext p
    change (Pi.single (Sum.inr i) 1 : (Fin q ⊕ Fin q) → K)
      (Sum.swap (finSumFinEquiv.symm p.1)) = _
    rw [show Sum.inr i = Sum.swap (Sum.inl i : Fin q ⊕ Fin q) from rfl,
      single_swap_reindex]
    simp [Pi.single_apply, Prod.ext_iff, Subsingleton.elim p.2 0]
  · ext p
    change (traceEval (K := K) (q := q))
      (Pi.single (Sum.inr (i,i)) 1 : (Fin 2 ⊕ (Fin q × Fin q)) → K) = _
    rw [trace_diag]
    rcases p with ⟨a,b⟩
    fin_cases a
    fin_cases b
    rfl

private theorem trace_right (i : Fin q) :
    PiTensorProduct.map (traceMaps (K := K))
      (monom (Sum.inr i) (Sum.inl i) (Sum.inr (i,i))) =
        mmMonom (finSumFinEquiv (Sum.inr i)) := by
  classical
  rw [monom, PiTensorProduct.map_tprod, mmMonom]
  congr 1
  funext s
  fin_cases s
  · ext p
    change (Pi.single (Sum.inr i) 1 : (Fin q ⊕ Fin q) → K) (finSumFinEquiv.symm p.2) = _
    rw [single_reindex]
    simp [Pi.single_apply, Prod.ext_iff, Subsingleton.elim p.1 0]
  · ext p
    change (Pi.single (Sum.inl i) 1 : (Fin q ⊕ Fin q) → K)
      (Sum.swap (finSumFinEquiv.symm p.1)) = _
    rw [show Sum.inl i = Sum.swap (Sum.inr i : Fin q ⊕ Fin q) from rfl,
      single_swap_reindex]
    simp [Pi.single_apply, Prod.ext_iff, Subsingleton.elim p.2 0]
  · ext p
    change (traceEval (K := K) (q := q))
      (Pi.single (Sum.inr (i,i)) 1 : (Fin 2 ⊕ (Fin q × Fin q)) → K) = _
    rw [trace_diag]
    rcases p with ⟨a,b⟩
    fin_cases a
    fin_cases b
    rfl

private theorem trace_tensor :
    PiTensorProduct.map (traceMaps (K := K) (q := q)) (coupledTensor K q) =
      MMTensor K 1 (q + q) 1 := by
  classical
  change PiTensorProduct.map (traceMaps (K := K))
    ((∑ i : Fin q, monom (K := K) (Sum.inl i) (Sum.inl i) (Sum.inl 0)) +
      (∑ k : Fin q, monom (K := K) (Sum.inr k) (Sum.inr k) (Sum.inl 1)) +
      (∑ i : Fin q, ∑ k : Fin q, monom (K := K) (Sum.inl i) (Sum.inr k) (Sum.inr (i,k))) +
      (∑ i : Fin q, ∑ k : Fin q, monom (K := K) (Sum.inr k) (Sum.inl i) (Sum.inr (i,k)))) = _
  simp only [map_add, map_sum]
  have hlow (x y : Fin q ⊕ Fin q) (w : Fin 2) :
      PiTensorProduct.map (traceMaps (K := K)) (monom x y (Sum.inl w)) = 0 :=
    trace_monom_zero x y _ (by simp)
  simp only [hlow, Finset.sum_const_zero, zero_add]
  have hcross (x y : Fin q ⊕ Fin q) (i k : Fin q) (hik : k ≠ i) :
      PiTensorProduct.map (traceMaps (K := K)) (monom x y (Sum.inr (i,k))) = 0 := by
    apply trace_monom_zero
    intro j h
    have hij := Sum.inr.inj h
    exact hik ((congrArg Prod.snd hij).trans (congrArg Prod.fst hij).symm)
  have hsumL (i : Fin q) : (∑ k, PiTensorProduct.map (traceMaps (K := K))
      (monom (Sum.inl i) (Sum.inr k) (Sum.inr (i,k)))) =
      mmMonom (K := K) (finSumFinEquiv (Sum.inl i)) := by
    rw [Finset.sum_eq_single i, trace_left]
    · intro k _ hk
      exact hcross _ _ i k hk
    · simp
  have hsumR (i : Fin q) : (∑ k, PiTensorProduct.map (traceMaps (K := K))
      (monom (Sum.inr k) (Sum.inl i) (Sum.inr (i,k)))) =
      mmMonom (K := K) (finSumFinEquiv (Sum.inr i)) := by
    rw [Finset.sum_eq_single i, trace_right]
    · intro k _ hk
      exact hcross _ _ i k hk
    · simp
  simp only [hsumL, hsumR]
  have hsum := finSumFinEquiv.sum_comp (mmMonom (K := K) (q := q))
  rw [Fintype.sum_sum_type] at hsum
  simpa only [MMTensor, Fin.sum_univ_one, mmMonom] using hsum

end MME.CoupledTrace

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

/-- Selecting target words after the map is equivalent to selecting their
preimages before it, even when the coordinate-label map is not injective. -/
theorem mme_kronPow_mode_map_word_projection
    {K : Type u} [Field K] {T S : TensorObj K 3} (i : Fin 3)
    {α β : Type u} (b : Basis α K (T.V i)) (c : Basis β K (S.V i))
    (f : T.V i →ₗ[K] S.V i) (g : α → β) (hf : ∀ a, f (b a) = c (g a))
    (N : ℕ) (keep : PowIndex β N → Prop) [DecidablePred keep] :
    let B := kronPowModeBasis T i b N
    let C := kronPowModeBasis S i c N
    let wordMap := fun w : PowIndex α N ↦
      PowIndex.ofFun N (fun r ↦ g (PowIndex.get N w r))
    let F := TensorObj.kronPowModeMap i f N
    (C.constr K (fun w ↦ if keep w then C w else 0)).comp F =
      F.comp (B.constr K (fun w ↦ if keep (wordMap w) then B w else 0)) := by
  dsimp only
  apply (kronPowModeBasis T i b N).ext
  intro w
  simp only [LinearMap.comp_apply, Basis.constr_basis,
    mme_kronPow_mode_map_word_basis i b c f g hf]
  split_ifs <;> simp [mme_kronPow_mode_map_word_basis i b c f g hf]

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

private theorem trace_word_letter_0
    {K : Type u} [Field K] (q : ℕ) (x : ULift.{u} (Fin q ⊕ Fin q)) :
    (MME.CoupledTrace.traceMaps (K := K) (q := q) 0)
      (((Pi.basisFun K (Fin q ⊕ Fin q)).reindex Equiv.ulift.symm :
        Basis (ULift.{u} (Fin q ⊕ Fin q)) K ((coupledObj K q).V 0)) x) =
    (((Pi.basisFun K (Fin 1 × Fin (q + q))).reindex Equiv.ulift.symm :
        Basis (ULift.{u} (Fin 1 × Fin (q + q))) K ((MMObj K 1 (q + q) 1).V 0))
      (⟨(0, finSumFinEquiv x.down)⟩ : ULift.{u} (Fin 1 × Fin (q + q)))) := by
  -- Unfold the tensor-object module instances when evaluating the coordinate basis.
  erw [Basis.reindex_apply, Basis.reindex_apply, Pi.basisFun_apply, Pi.basisFun_apply]
  funext p
  change (Pi.single x.down 1 : (Fin q ⊕ Fin q) → K)
    (finSumFinEquiv.symm p.2) = _
  rw [MME.CoupledTrace.single_reindex]
  simp [Pi.single_apply, Prod.ext_iff, Subsingleton.elim p.1 0]

private theorem trace_word_letter_1
    {K : Type u} [Field K] (q : ℕ) (x : ULift.{u} (Fin q ⊕ Fin q)) :
    (MME.CoupledTrace.traceMaps (K := K) (q := q) 1)
      (((Pi.basisFun K (Fin q ⊕ Fin q)).reindex Equiv.ulift.symm :
        Basis (ULift.{u} (Fin q ⊕ Fin q)) K ((coupledObj K q).V 1)) x) =
    (((Pi.basisFun K (Fin (q + q) × Fin 1)).reindex Equiv.ulift.symm :
        Basis (ULift.{u} (Fin (q + q) × Fin 1)) K ((MMObj K 1 (q + q) 1).V 1))
      (⟨(finSumFinEquiv (Sum.swap x.down), 0)⟩ : ULift.{u} (Fin (q + q) × Fin 1))) := by
  -- Unfold the tensor-object module instances when evaluating the coordinate basis.
  erw [Basis.reindex_apply, Basis.reindex_apply, Pi.basisFun_apply, Pi.basisFun_apply]
  funext p
  change (Pi.single x.down 1 : (Fin q ⊕ Fin q) → K)
    (Sum.swap (finSumFinEquiv.symm p.1)) = _
  have hx : x.down = Sum.swap (Sum.swap x.down) := by simp
  rw [hx, MME.CoupledTrace.single_swap_reindex]
  simp [Pi.single_apply, Prod.ext_iff, Subsingleton.elim p.2 0]

/-- Trace gives power restriction maps whose first two mode actions retain
all numerical letters and explicitly track the binary label swap. -/
theorem mme_coupled_trace_power_restriction_word_basis_maps
    {K : Type u} [Field K] (q : ℕ) :
    let T := coupledObj K q
    let S := MMObj K 1 (q + q) 1
    let b0 := (Pi.basisFun K (Fin q ⊕ Fin q)).reindex Equiv.ulift.symm
    let b1 := (Pi.basisFun K (Fin q ⊕ Fin q)).reindex Equiv.ulift.symm
    let c0 := (Pi.basisFun K (Fin 1 × Fin (q + q))).reindex Equiv.ulift.symm
    let c1 := (Pi.basisFun K (Fin (q + q) × Fin 1)).reindex Equiv.ulift.symm
    ∃ f : ∀ i, T.V i →ₗ[K] S.V i,
      (∀ N, PiTensorProduct.map (fun i ↦ TensorObj.kronPowModeMap i (f i) N)
        (T.kronPow N).t = (S.kronPow N).t) ∧
      (∀ N (w : PowIndex (ULift.{u} (Fin q ⊕ Fin q)) N),
        TensorObj.kronPowModeMap 0 (f 0) N (kronPowModeBasis T 0 b0 N w) =
          kronPowModeBasis S 0 c0 N (PowIndex.ofFun N (fun r ↦
            (⟨(0, finSumFinEquiv (PowIndex.get N w r).down)⟩ :
              ULift.{u} (Fin 1 × Fin (q + q)))))) ∧
      (∀ N (w : PowIndex (ULift.{u} (Fin q ⊕ Fin q)) N),
        TensorObj.kronPowModeMap 1 (f 1) N (kronPowModeBasis T 1 b1 N w) =
          kronPowModeBasis S 1 c1 N (PowIndex.ofFun N (fun r ↦
            (⟨(finSumFinEquiv (Sum.swap (PowIndex.get N w r).down), 0)⟩ :
              ULift.{u} (Fin (q + q) × Fin 1))))) := by
  dsimp only
  refine ⟨MME.CoupledTrace.traceMaps (K := K) (q := q), ?_, ?_, ?_⟩
  · exact fun N ↦ power_tensor_map (T := coupledObj K q) (S := MMObj K 1 (q + q) 1)
      (MME.CoupledTrace.traceMaps (K := K) (q := q))
      (MME.CoupledTrace.trace_tensor (K := K) (q := q)) N
  · intro N w
    refine mme_kronPow_mode_map_word_basis (T := coupledObj K q)
      (S := MMObj K 1 (q + q) 1) 0
      ((Pi.basisFun K (Fin q ⊕ Fin q)).reindex Equiv.ulift.symm)
      ((Pi.basisFun K (Fin 1 × Fin (q + q))).reindex Equiv.ulift.symm)
      (MME.CoupledTrace.traceMaps (K := K) (q := q) 0)
      (fun x : ULift.{u} (Fin q ⊕ Fin q) ↦
        (⟨(0, finSumFinEquiv x.down)⟩ : ULift.{u} (Fin 1 × Fin (q + q)))) ?_ N w
    exact trace_word_letter_0 q
  · intro N w
    refine mme_kronPow_mode_map_word_basis (T := coupledObj K q)
      (S := MMObj K 1 (q + q) 1) 1
      ((Pi.basisFun K (Fin q ⊕ Fin q)).reindex Equiv.ulift.symm)
      ((Pi.basisFun K (Fin (q + q) × Fin 1)).reindex Equiv.ulift.symm)
      (MME.CoupledTrace.traceMaps (K := K) (q := q) 1)
      (fun x : ULift.{u} (Fin q ⊕ Fin q) ↦
        (⟨(finSumFinEquiv (Sum.swap x.down), 0)⟩ :
          ULift.{u} (Fin (q + q) × Fin 1))) ?_ N w
    exact trace_word_letter_1 q
private theorem permuted_power_trace
    {K : Type u} [Field K] (q N : ℕ) (σ : Equiv.Perm (Fin 3)) :
    PiTensorProduct.map
      (fun i ↦ TensorObj.kronPowModeMap i
        (MME.CoupledTrace.traceMaps (K := K) (q := q) (σ.symm i)) N)
      ((TensorObj.permObj σ (coupledObj K q)).kronPow N).t =
      ((TensorObj.permObj σ (MMObj K 1 (q + q) 1)).kronPow N).t := by
  apply power_tensor_map
    (T := TensorObj.permObj σ (coupledObj K q))
    (S := TensorObj.permObj σ (MMObj K 1 (q + q) 1))
  change PiTensorProduct.map _ (PiTensorProduct.reindex K _ σ _) =
    PiTensorProduct.reindex K _ σ _
  rw [PiTensorProduct.map_reindex]
  exact congrArg (PiTensorProduct.reindex K _ σ)
    (MME.CoupledTrace.trace_tensor (K := K) (q := q))

/-- The paired trace maps preserve the tensor and explicitly map the complete
third-coordinate word basis, including all numerical letters. -/
theorem mme_coupled_paired_trace_word_basis_maps
    {K : Type u} [Field K] (q N : ℕ) :
    let L := TensorObj.permObj (cyclicPerm.trans cyclicPerm) (coupledObj K q)
    let R := TensorObj.permObj cyclicPerm (coupledObj K q)
    let U := TensorObj.permObj (cyclicPerm.trans cyclicPerm) (MMObj K 1 (q + q) 1)
    let V := TensorObj.permObj cyclicPerm (MMObj K 1 (q + q) 1)
    let b := (Pi.basisFun K (Fin q ⊕ Fin q)).reindex Equiv.ulift.symm
    let c := (Pi.basisFun K (Fin 1 × Fin (q + q))).reindex Equiv.ulift.symm
    let e := (Pi.basisFun K (Fin (q + q) × Fin 1)).reindex Equiv.ulift.symm
    let g0 := fun w : PowIndex (ULift.{u} (Fin q ⊕ Fin q)) N ↦
      PowIndex.ofFun N (fun r ↦ (⟨(0, finSumFinEquiv (PowIndex.get N w r).down)⟩ :
        ULift.{u} (Fin 1 × Fin (q + q))))
    let g1 := fun w : PowIndex (ULift.{u} (Fin q ⊕ Fin q)) N ↦
      PowIndex.ofFun N (fun r ↦
        (⟨(finSumFinEquiv (Sum.swap (PowIndex.get N w r).down), 0)⟩ :
          ULift.{u} (Fin (q + q) × Fin 1)))
    ∃ F : ∀ i, ((L.kronPow N).kron (R.kronPow N)).V i →ₗ[K]
        ((U.kronPow N).kron (V.kronPow N)).V i,
      PiTensorProduct.map F ((L.kronPow N).kron (R.kronPow N)).t =
        ((U.kronPow N).kron (V.kronPow N)).t ∧
      ∀ x y, F 2
        ((kronPowModeBasis L 2 b N x) ⊗ₜ[K] (kronPowModeBasis R 2 b N y)) =
        (kronPowModeBasis U 2 c N (g0 x)) ⊗ₜ[K]
          (kronPowModeBasis V 2 e N (g1 y)) := by
  dsimp only
  let f := MME.CoupledTrace.traceMaps (K := K) (q := q)
  refine ⟨fun i ↦ TensorProduct.map
    (TensorObj.kronPowModeMap i (f ((cyclicPerm.trans cyclicPerm).symm i)) N)
    (TensorObj.kronPowModeMap i (f (cyclicPerm.symm i)) N), ?_, ?_⟩
  · change PiTensorProduct.map _ (MME.interchange _ _) = MME.interchange _ _
    rw [TensorObj.TypeGrading.kronMap_interchange]
    rw [permuted_power_trace, permuted_power_trace]
  · intro x y
    dsimp only
    set_option backward.isDefEq.respectTransparency false in
      erw [TensorProduct.map_tmul]
    have hx := mme_kronPow_mode_map_word_basis
      (T := TensorObj.permObj (cyclicPerm.trans cyclicPerm) (coupledObj K q))
      (S := TensorObj.permObj (cyclicPerm.trans cyclicPerm) (MMObj K 1 (q + q) 1))
      2 ((Pi.basisFun K (Fin q ⊕ Fin q)).reindex Equiv.ulift.symm)
      ((Pi.basisFun K (Fin 1 × Fin (q + q))).reindex Equiv.ulift.symm)
      (f 0) (fun a : ULift.{u} (Fin q ⊕ Fin q) ↦
        (⟨(0, finSumFinEquiv a.down)⟩ : ULift.{u} (Fin 1 × Fin (q + q))))
      (trace_word_letter_0 q) N x
    have hy := mme_kronPow_mode_map_word_basis
      (T := TensorObj.permObj cyclicPerm (coupledObj K q))
      (S := TensorObj.permObj cyclicPerm (MMObj K 1 (q + q) 1))
      2 ((Pi.basisFun K (Fin q ⊕ Fin q)).reindex Equiv.ulift.symm)
      ((Pi.basisFun K (Fin (q + q) × Fin 1)).reindex Equiv.ulift.symm)
      (f 1) (fun a : ULift.{u} (Fin q ⊕ Fin q) ↦
        (⟨(finSumFinEquiv (Sum.swap a.down), 0)⟩ : ULift.{u} (Fin (q + q) × Fin 1)))
      (trace_word_letter_1 q) N y
    exact congrArg₂ (fun a b ↦ a ⊗ₜ[K] b) hx hy

/-- Commuting coordinate maps transport a restriction after applying projections. -/
theorem mme_tensor_projection_restriction
    {K : Type u} [Field K] {d : ℕ} {T S : TensorObj K d}
    (f : ∀ i, T.V i →ₗ[K] S.V i)
    (hf : PiTensorProduct.map f T.t = S.t)
    (P : ∀ i, T.V i →ₗ[K] T.V i)
    (Q : ∀ i, S.V i →ₗ[K] S.V i)
    (hcomm : ∀ i, (Q i).comp (f i) = (f i).comp (P i)) :
    TensorObj.Restrict { S with t := PiTensorProduct.map Q S.t }
      { T with t := PiTensorProduct.map P T.t } := by
  refine ⟨f, ?_⟩
  change PiTensorProduct.map f (PiTensorProduct.map P T.t) =
    PiTensorProduct.map Q S.t
  rw [← LinearMap.comp_apply, ← PiTensorProduct.map_comp]
  simp_rw [← hcomm]
  rw [PiTensorProduct.map_comp, LinearMap.comp_apply, hf]

/-- A map specified on bases commutes with retaining any set of target labels
and its preimage among source labels. Injectivity is not required. -/
theorem mme_basis_map_projection
    {K : Type u} [Field K] {V W : Type u}
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    {α β : Type u} (b : Basis α K V) (c : Basis β K W)
    (f : V →ₗ[K] W) (g : α → β) (hf : ∀ a, f (b a) = c (g a))
    (keep : β → Prop) [DecidablePred keep] :
    (c.constr K (fun a ↦ if keep a then c a else 0)).comp f =
      f.comp (b.constr K (fun a ↦ if keep (g a) then b a else 0)) := by
  apply b.ext
  intro a
  simp only [LinearMap.comp_apply, Basis.constr_basis, hf]
  split_ifs <;> simp [hf]

/-- Simultaneous basis projections preserve a restriction when each coordinate
map carries source basis vectors to the specified target basis vectors. -/
theorem mme_tensor_basis_projection_restriction
    {K : Type u} [Field K] {d : ℕ} {T S : TensorObj K d}
    {α β : Fin d → Type u}
    (b : ∀ i, Basis (α i) K (T.V i)) (c : ∀ i, Basis (β i) K (S.V i))
    (f : ∀ i, T.V i →ₗ[K] S.V i) (g : ∀ i, α i → β i)
    (hf : PiTensorProduct.map f T.t = S.t)
    (hb : ∀ i a, f i (b i a) = c i (g i a))
    (keep : ∀ i, β i → Prop) [∀ i, DecidablePred (keep i)] :
    TensorObj.Restrict
      { S with t := (PiTensorProduct.map
        (fun i ↦ (c i).constr K (fun a ↦ if keep i a then c i a else 0)) S.t) }
      { T with t := (PiTensorProduct.map
        (fun i ↦ (b i).constr K (fun a ↦ if keep i (g i a) then b i a else 0)) T.t) } := by
  apply mme_tensor_projection_restriction f hf
  intro i
  exact mme_basis_map_projection (b i) (c i) (f i) (g i) (hb i) (keep i)

/-- Projecting one coordinate commutes with a restriction when its basis labels
are transported by the coordinate map. The other coordinates are unrestricted. -/
theorem mme_tensor_single_basis_projection_restriction
    {K : Type u} [Field K] {d : ℕ} {T S : TensorObj K d}
    (j : Fin d) {α β : Type u}
    (b : Basis α K (T.V j)) (c : Basis β K (S.V j))
    (f : ∀ i, T.V i →ₗ[K] S.V i) (g : α → β)
    (hf : PiTensorProduct.map f T.t = S.t)
    (hb : ∀ a, f j (b a) = c (g a))
    (keep : β → Prop) [DecidablePred keep] :
    TensorObj.Restrict
      { S with t := (PiTensorProduct.map
          (Function.update (fun _ ↦ LinearMap.id) j
            (c.constr K (fun a ↦ if keep a then c a else 0))) S.t) }
      { T with t := (PiTensorProduct.map
          (Function.update (fun _ ↦ LinearMap.id) j
            (b.constr K (fun a ↦ if keep (g a) then b a else 0))) T.t) } := by
  apply mme_tensor_projection_restriction f hf
  intro i
  by_cases h : i = j
  · subst i
    simp only [Function.update_self]
    exact mme_basis_map_projection b c (f j) g hb keep
  · simp [Function.update_of_ne h]

/-- The paired trace restriction descends through any target word-pair selection
and its preimage in the coupled word basis. -/
theorem mme_coupled_paired_trace_word_projection_restriction
    {K : Type u} [Field K] (q N : ℕ)
    (keep : (PowIndex (ULift.{u} (Fin 1 × Fin (q + q))) N ×
      PowIndex (ULift.{u} (Fin (q + q) × Fin 1)) N) → Prop)
    [DecidablePred keep] :
    let L := TensorObj.permObj (cyclicPerm.trans cyclicPerm) (coupledObj K q)
    let R := TensorObj.permObj cyclicPerm (coupledObj K q)
    let U := TensorObj.permObj (cyclicPerm.trans cyclicPerm) (MMObj K 1 (q + q) 1)
    let V := TensorObj.permObj cyclicPerm (MMObj K 1 (q + q) 1)
    let b := (Pi.basisFun K (Fin q ⊕ Fin q)).reindex Equiv.ulift.symm
    let c := (Pi.basisFun K (Fin 1 × Fin (q + q))).reindex Equiv.ulift.symm
    let e := (Pi.basisFun K (Fin (q + q) × Fin 1)).reindex Equiv.ulift.symm
    let g0 := fun w : PowIndex (ULift.{u} (Fin q ⊕ Fin q)) N ↦
      PowIndex.ofFun N (fun r ↦ (⟨(0, finSumFinEquiv (PowIndex.get N w r).down)⟩ :
        ULift.{u} (Fin 1 × Fin (q + q))))
    let g1 := fun w : PowIndex (ULift.{u} (Fin q ⊕ Fin q)) N ↦
      PowIndex.ofFun N (fun r ↦
        (⟨(finSumFinEquiv (Sum.swap (PowIndex.get N w r).down), 0)⟩ :
          ULift.{u} (Fin (q + q) × Fin 1)))
    let B := (kronPowModeBasis L 2 b N).tensorProduct (kronPowModeBasis R 2 b N)
    let C := (kronPowModeBasis U 2 c N).tensorProduct (kronPowModeBasis V 2 e N)
    let source := (L.kronPow N).kron (R.kronPow N)
    let target := (U.kronPow N).kron (V.kronPow N)
    TensorObj.Restrict
      { target with t := (PiTensorProduct.map
          (Function.update (fun _ ↦ LinearMap.id) 2
            (C.constr K (fun w ↦ if keep w then C w else 0))) target.t) }
      { source with t := (PiTensorProduct.map
          (Function.update (fun _ ↦ LinearMap.id) 2
            (B.constr K (fun w ↦ if keep (g0 w.1, g1 w.2) then B w else 0))) source.t) } := by
  dsimp only
  obtain ⟨F, hF, hb⟩ := mme_coupled_paired_trace_word_basis_maps (K := K) q N
  refine mme_tensor_single_basis_projection_restriction 2 _ _ F _ hF ?_ keep
  rintro ⟨x, y⟩
  set_option backward.isDefEq.respectTransparency false in
    erw [Basis.tensorProduct_apply, Basis.tensorProduct_apply]
  exact hb x y

/-- Every source word-pair selection transfers through the paired trace map.
The inverse label formulas describe precisely which matrix words survive. -/
theorem solution
    {K : Type u} [Field K] (q N : ℕ)
    (keep : (PowIndex (ULift.{u} (Fin q ⊕ Fin q)) N ×
      PowIndex (ULift.{u} (Fin q ⊕ Fin q)) N) → Prop)
    [DecidablePred keep] :
    let L := TensorObj.permObj (cyclicPerm.trans cyclicPerm) (coupledObj K q)
    let R := TensorObj.permObj cyclicPerm (coupledObj K q)
    let U := TensorObj.permObj (cyclicPerm.trans cyclicPerm) (MMObj K 1 (q + q) 1)
    let V := TensorObj.permObj cyclicPerm (MMObj K 1 (q + q) 1)
    let b := (Pi.basisFun K (Fin q ⊕ Fin q)).reindex Equiv.ulift.symm
    let c := (Pi.basisFun K (Fin 1 × Fin (q + q))).reindex Equiv.ulift.symm
    let e := (Pi.basisFun K (Fin (q + q) × Fin 1)).reindex Equiv.ulift.symm
    let h0 := fun w : PowIndex (ULift.{u} (Fin 1 × Fin (q + q))) N ↦
      PowIndex.ofFun N (fun r ↦
        (⟨finSumFinEquiv.symm (PowIndex.get N w r).down.2⟩ : ULift.{u} (Fin q ⊕ Fin q)))
    let h1 := fun w : PowIndex (ULift.{u} (Fin (q + q) × Fin 1)) N ↦
      PowIndex.ofFun N (fun r ↦
        (⟨Sum.swap (finSumFinEquiv.symm (PowIndex.get N w r).down.1)⟩ :
          ULift.{u} (Fin q ⊕ Fin q)))
    let B := (kronPowModeBasis L 2 b N).tensorProduct (kronPowModeBasis R 2 b N)
    let C := (kronPowModeBasis U 2 c N).tensorProduct (kronPowModeBasis V 2 e N)
    let source := (L.kronPow N).kron (R.kronPow N)
    let target := (U.kronPow N).kron (V.kronPow N)
    TensorObj.Restrict
      { target with t := (PiTensorProduct.map
          (Function.update (fun _ ↦ LinearMap.id) 2
            (C.constr K (fun w ↦ if keep (h0 w.1, h1 w.2) then C w else 0))) target.t) }
      { source with t := (PiTensorProduct.map
          (Function.update (fun _ ↦ LinearMap.id) 2
            (B.constr K (fun w ↦ if keep w then B w else 0))) source.t) } := by
  intro L R U V b c e h0 h1 B C source target
  have hinv0 (w : PowIndex (ULift.{u} (Fin q ⊕ Fin q)) N) :
      h0 (PowIndex.ofFun N (fun r ↦
        (⟨(0, finSumFinEquiv (PowIndex.get N w r).down)⟩ :
          ULift.{u} (Fin 1 × Fin (q + q))))) = w := by
    dsimp only [h0]
    simp only [PowIndex.get_ofFun, Equiv.symm_apply_apply]
    exact PowIndex.ofFun_get N w
  have hinv1 (w : PowIndex (ULift.{u} (Fin q ⊕ Fin q)) N) :
      h1 (PowIndex.ofFun N (fun r ↦
        (⟨(finSumFinEquiv (Sum.swap (PowIndex.get N w r).down), 0)⟩ :
          ULift.{u} (Fin (q + q) × Fin 1)))) = w := by
    dsimp only [h1]
    simp only [PowIndex.get_ofFun, Equiv.symm_apply_apply, Sum.swap_swap]
    exact PowIndex.ofFun_get N w
  have h := mme_coupled_paired_trace_word_projection_restriction
    (K := K) q N (fun w ↦ keep (h0 w.1, h1 w.2))
  dsimp only at h
  simpa only [hinv0, hinv1] using h

#print axioms solution
