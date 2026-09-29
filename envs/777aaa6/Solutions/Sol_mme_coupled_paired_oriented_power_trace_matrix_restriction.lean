-- Prove2me | solution 1 for mme_coupled_paired_oriented_power_trace_matrix_restriction
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T02:28:36.543985+00:00
-- url     : https://prove2.me/submissions/6d598eb4-1e73-4b3a-b1f9-be719b638c09

import Definitions.Def_mme_TypeGrading_kron
import Definitions.Def_mme_permutation
import Theorems.Thm_mme_MMObj_permObj_cyclic_sq
import Definitions.Def_mme_CW_coupled_value
import Definitions.Def_mme_tensor_rank
import Mathlib.Tactic.FinCases

open MME PiTensorProduct BigOperators
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

private theorem kron_restrict {X X' Y Y' : TensorObj K 3}
    (hX : TensorObj.Restrict X X') (hY : TensorObj.Restrict Y Y') :
    TensorObj.Restrict (TensorObj.kron X Y) (TensorObj.kron X' Y') := by
  obtain ⟨f, hf⟩ := hX
  obtain ⟨g, hg⟩ := hY
  refine ⟨fun i ↦ TensorProduct.map (f i) (g i), ?_⟩
  change PiTensorProduct.map (fun i ↦ TensorProduct.map (f i) (g i))
    (MME.interchange X'.t Y'.t) = MME.interchange X.t Y.t
  rw [TensorObj.TypeGrading.kronMap_interchange, hf, hg]

private theorem unit_matrix_restrict :
    TensorObj.Restrict (MMObj K 1 1 1) (TensorObj.oneObj : TensorObj K 3) := by
  let f : ∀ i : Fin 3, K →ₗ[K] MMSpace K 1 1 1 i
    | ⟨0, _⟩ => LinearMap.pi (fun _ ↦ LinearMap.id)
    | ⟨1, _⟩ => LinearMap.pi (fun _ ↦ LinearMap.id)
    | ⟨2, _⟩ => LinearMap.pi (fun _ ↦ LinearMap.id)
  refine ⟨f, ?_⟩
  change PiTensorProduct.map f (tprod K (fun _ ↦ (1 : K))) = MMTensor K 1 1 1
  simp only [PiTensorProduct.map_tprod, MMTensor, Fin.sum_univ_one]
  congr 1
  funext i
  fin_cases i <;> ext p <;> rcases p with ⟨a,b⟩ <;>
    fin_cases a <;> fin_cases b <;> simp [f, LinearMap.pi]

private theorem matrix_power_restrict {X : TensorObj K 3} {a b c : ℕ}
    (h : TensorObj.Restrict (MMObj K a b c) X) (N : ℕ) :
    TensorObj.Restrict (MMObj K (a ^ N) (b ^ N) (c ^ N)) (X.kronPow N) := by
  induction N with
  | zero => simpa only [pow_zero, TensorObj.kronPow] using unit_matrix_restrict (K := K)
  | succ N ih =>
    have hh := (MMObj_kron_iso (K := K) a b c (a ^ N) (b ^ N) (c ^ N)).2.trans
      (kron_restrict h ih)
    simpa only [TensorObj.kronPow, pow_succ, Nat.mul_comm] using hh

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

noncomputable def mmMonom (j : Fin (q + q)) : PiTensorProduct K (MMSpace K 1 (q+q) 1) :=
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
      MMTensor K 1 (q+q) 1 := by
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


/-- Trace in the third mode keeps both copies of all numerical labels. -/
theorem mme_coupled_trace_matrix_restriction
    {K : Type u} [Field K] (q : ℕ) :
    TensorObj.Restrict (MMObj K 1 (q + q) 1) (coupledObj K q) := by
  exact ⟨MME.CoupledTrace.traceMaps, MME.CoupledTrace.trace_tensor⟩

/-- Independent trace restrictions in the two oriented powers give an
aggregate block retaining both binary and numerical row and column labels. -/
theorem solution
    {K : Type u} [Field K] (q N : ℕ) :
    TensorObj.Restrict (MMObj K ((2 * q) ^ N) 1 ((2 * q) ^ N))
      (TensorObj.kron
        ((TensorObj.permObj (cyclicPerm.trans cyclicPerm) (coupledObj K q)).kronPow N)
        ((TensorObj.permObj cyclicPerm (coupledObj K q)).kronPow N)) := by
  have h := mme_coupled_trace_matrix_restriction (K := K) q
  have hl := (mme_MMObj_permObj_cyclic_sq (K := K) 1 (q+q) 1).2.trans
    (TensorObj.permObj_restrict (cyclicPerm.trans cyclicPerm) h)
  have hr := (MMObj_permObj_cyclic (K := K) 1 (q+q) 1).2.trans
    (TensorObj.permObj_restrict cyclicPerm h)
  have hlN := MME.CoupledTrace.matrix_power_restrict hl N
  have hrN := MME.CoupledTrace.matrix_power_restrict hr N
  simp only [one_pow] at hlN hrN
  have hh := (MMObj_kron_iso (K := K) ((q+q) ^ N) 1 1 1 1 ((q+q) ^ N)).2.trans
    (MME.CoupledTrace.kron_restrict hlN hrN)
  simpa only [Nat.mul_one, Nat.one_mul, two_mul] using hh
