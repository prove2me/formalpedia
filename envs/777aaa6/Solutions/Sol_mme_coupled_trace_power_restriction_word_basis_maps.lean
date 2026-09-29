-- Prove2me | solution 1 for mme_coupled_trace_power_restriction_word_basis_maps
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T02:39:09.494775+00:00
-- url     : https://prove2.me/submissions/85ec770c-cd27-4bb2-bd11-dff41d16f50e

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
theorem solution
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