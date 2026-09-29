-- Prove2me | solution 1 for mme_CW_Phi_coeff_two
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-06-05T01:49:07.77293+00:00
-- url     : https://prove2.me/submissions/62f5ba69-80fe-489d-a610-eda8dde6a48c

import Theorems.Thm_mme_CW_Phi_coeff_two

/-! # Solution: CW Phi order-2 coefficient identity (the main case)

This file proves the order-2 cross-term cancellation step for the CW
border-rank `IsSquare` argument.  The witness is the Filmus-style
γ-construction:

* `q` middle slots `polyMid i`: symmetric `e_O + ε · e_{M_i}` per mode.
* boundary slot `polyBdry`: symmetric `e_O + ε · γ · E + ε² · e_T` per mode.
* compensation slot `polyComp`: mode-asymmetric, with mode-0 scalar
  `-(q+2)` and degree-1 correction `-(1+γ) · E`, modes 1, 2 scalar `1`
  with degree-1 correction `(1+γ)/(q+2) · E`.

Under the algebraic constraint `(q+2)·γ² = (1+γ)²` the off-diagonal
order-2 cross terms `E ⊗ E ⊗ e_O + cyclic` cancel, and the surviving
contribution is exactly `CWTensor K (q+1)`.

The proof is fully concrete: order-0 cancellation `-(q+2) + (q+1) + 1 = 0`,
order-1 cancellation `-(1+γ) + 1 + γ = 0` per mode, and order-2 by
six-tuple expansion + cancellation `(q+2)·γ² - (1+γ)² = 0`.
-/

open MME PiTensorProduct BigOperators Finset

universe u

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

namespace MME.CWPhiCoeffTwoSol

variable {K : Type u} [Field K]
variable (q : ℕ)

/-- Standard basis vector `e_j : Fin (q+2) → K`. -/
private noncomputable def e (j : Fin (q + 2)) : Fin (q + 2) → K := Pi.single j 1

/-- The "zero" index `0 : Fin (q+2)`. -/
private def O : Fin (q + 2) := ⟨0, by omega⟩

/-- The "top" index `q+1 : Fin (q+2)`. -/
private def T : Fin (q + 2) := ⟨q + 1, by omega⟩

/-- The "middle" index `i : Fin q ↪ Fin (q+2)` shifting by 1. -/
private def M (i : Fin q) : Fin (q + 2) := ⟨i.val + 1, by omega⟩

/-- The CW source space at each mode. -/
private abbrev V (i : Fin 3) : Type u := (CWObj K q).V i

private noncomputable def eO (s : Fin 3) : V (K := K) q s :=
  match s with
  | ⟨0, _⟩ => e (K := K) q (O q)
  | ⟨1, _⟩ => e (K := K) q (O q)
  | ⟨2, _⟩ => e (K := K) q (O q)

private noncomputable def eT (s : Fin 3) : V (K := K) q s :=
  match s with
  | ⟨0, _⟩ => e (K := K) q (T q)
  | ⟨1, _⟩ => e (K := K) q (T q)
  | ⟨2, _⟩ => e (K := K) q (T q)

end MME.CWPhiCoeffTwoSol

namespace MME.CWPhiCoeffTwoSol

open MME.CWPhiCoeffTwoSol

variable {K : Type u} [Field K]

/-- `E := ∑_{i : Fin (q+1)} e_{M_i}` at each mode. -/
private noncomputable def E (q : ℕ) (s : Fin 3) : V (K := K) (q + 1) s :=
  match s with
  | ⟨0, _⟩ => ∑ i : Fin (q + 1), e (K := K) (q + 1) (M (q + 1) i)
  | ⟨1, _⟩ => ∑ i : Fin (q + 1), e (K := K) (q + 1) (M (q + 1) i)
  | ⟨2, _⟩ => ∑ i : Fin (q + 1), e (K := K) (q + 1) (M (q + 1) i)

private noncomputable def eM (q : ℕ) (i : Fin (q + 1)) (s : Fin 3) :
    V (K := K) (q + 1) s :=
  match s with
  | ⟨0, _⟩ => e (K := K) (q + 1) (M (q + 1) i)
  | ⟨1, _⟩ => e (K := K) (q + 1) (M (q + 1) i)
  | ⟨2, _⟩ => e (K := K) (q + 1) (M (q + 1) i)

private noncomputable def polyMid (q : ℕ) (i : Fin (q + 1)) (s : Fin 3) :
    ℕ →₀ V (K := K) (q + 1) s :=
  Finsupp.single 0 (eO (K := K) (q + 1) s) + Finsupp.single 1 (eM (K := K) q i s)

private noncomputable def polyBdry (q : ℕ) (γ : K) (s : Fin 3) :
    ℕ →₀ V (K := K) (q + 1) s :=
  Finsupp.single 0 (eO (K := K) (q + 1) s) +
  Finsupp.single 1 (γ • E (K := K) q s) +
  Finsupp.single 2 (eT (K := K) (q + 1) s)

private noncomputable def polyComp (q : ℕ) (γ : K) (s : Fin 3) :
    ℕ →₀ V (K := K) (q + 1) s :=
  Finsupp.single 0 (if s.val = 0
                    then -((q + 2 : K)) • eO (K := K) (q + 1) s
                    else eO (K := K) (q + 1) s) +
  Finsupp.single 1 (if s.val = 0
                    then -((1 + γ) • E (K := K) q s)
                    else ((1 + γ) / (q + 2 : K)) • E (K := K) q s)

private noncomputable def vfun (q : ℕ) (γ : K) (j : Fin ((q + 1) + 2)) (s : Fin 3) :
    ℕ →₀ V (K := K) (q + 1) s :=
  if h0 : j.val = 0 then polyComp (K := K) q γ s
  else if hT : j.val = q + 2 then polyBdry (K := K) q γ s
  else polyMid (K := K) q ⟨j.val - 1, by omega⟩ s

private lemma vlin_support (q : ℕ) (γ : K) (s : Fin 3) :
    ∀ k : ℕ, ((Pi.basisFun K (Fin ((q + 1) + 2))).constr K
        (fun j => vfun (K := K) q γ j s k)) ≠ 0 →
      k ∈ Finset.univ.biUnion
        (fun j : Fin ((q + 1) + 2) => (vfun (K := K) q γ j s).support) := by
  intro k hne
  rw [Finset.mem_biUnion]
  by_contra hall; push Not at hall
  apply hne
  have hz : (fun j : Fin ((q + 1) + 2) => (vfun (K := K) q γ j s) k) = 0 :=
    funext fun j => Finsupp.notMem_support_iff.mp (hall j (Finset.mem_univ j))
  rw [hz]; exact map_zero _

/-- The `PolyFamily` realising the CW γ-construction. -/
private noncomputable def Phi (q : ℕ) (γ : K) :
    PolyFamily (CWObj K (q + 1)) (TensorObj.diagObj K 3 ((q + 1) + 2)) where
  A := fun s => Finsupp.onFinset _ (fun k =>
        (Pi.basisFun K (Fin ((q + 1) + 2))).constr K
          (fun j => vfun (K := K) q γ j s k))
        (vlin_support (K := K) q γ s)

private lemma Phi_A_apply (q : ℕ) (γ : K) (s : Fin 3) (k : ℕ) :
    (Phi (K := K) q γ).A s k =
      (Pi.basisFun K (Fin ((q + 1) + 2))).constr K
        (fun j => vfun (K := K) q γ j s k) := rfl

private lemma vlin_single (q : ℕ) (γ : K) (s : Fin 3) (k : ℕ)
    (j : Fin ((q + 1) + 2)) :
    ((Pi.basisFun K (Fin ((q + 1) + 2))).constr K
        (fun j' => vfun (K := K) q γ j' s k)) (Pi.single j 1) =
      (vfun q γ j s) k := by
  rw [show (Pi.single j (1 : K) : Fin ((q+1)+2) → K)
        = (Pi.basisFun K (Fin ((q+1)+2))) j from
    (Pi.basisFun_apply K (Fin ((q+1)+2)) j).symm]
  exact Module.Basis.constr_basis (Pi.basisFun K (Fin ((q+1)+2))) K _ j

private lemma Phi_coeff_expand (q : ℕ) (γ : K) (k : ℕ) :
    (Phi (K := K) q γ).coeff k = ∑ j : Fin ((q + 1) + 2),
      (Finset.Nat.antidiagonalTuple 3 k).sum
        (fun m => tprod K (fun i => (vfun (K := K) q γ j i) (m i))) := by
  unfold PolyFamily.coeff
  have hY : (TensorObj.diagObj K 3 ((q+1)+2)).t =
      ∑ j : Fin ((q+1)+2),
        tprod K (fun (_ : Fin 3) => (Pi.single j 1 : Fin ((q+1)+2) → K)) := rfl
  simp_rw [hY]
  rw [Finset.sum_congr rfl (fun m _ =>
    map_sum (PiTensorProduct.map (fun i => (Phi (K := K) q γ).A i (m i)))
      (fun j : Fin ((q+1)+2) =>
        tprod K fun _ => (Pi.single j 1 : Fin ((q+1)+2) → K)) Finset.univ),
    Finset.sum_comm]
  congr 1; ext j; congr 1; ext m
  have hmap := PiTensorProduct.map_tprod (R := K)
    (f := fun i => (Phi (K := K) q γ).A i (m i))
    (x := fun _ : Fin 3 => (Pi.single j 1 : Fin ((q+1)+2) → K))
  refine hmap.trans ?_
  congr 1; funext i
  rw [Phi_A_apply]
  exact vlin_single q γ i (m i) j

/-! ## Reindexing the slot sum -/

private def slotToFin (q : ℕ) :
    (Unit ⊕ Fin (q + 1)) ⊕ Unit → Fin ((q + 1) + 2)
  | Sum.inl (Sum.inl ()) => ⟨0, by omega⟩
  | Sum.inl (Sum.inr i) => ⟨i.val + 1, by have := i.isLt; omega⟩
  | Sum.inr () => ⟨q + 2, by omega⟩

private def jPred (q : ℕ) (j : Fin ((q + 1) + 2)) : Fin (q + 1) :=
  ⟨(j.val - 1) % (q + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩

private def finToSlot (q : ℕ) : Fin ((q + 1) + 2) → (Unit ⊕ Fin (q + 1)) ⊕ Unit :=
  fun j =>
    if j.val = 0 then Sum.inl (Sum.inl ())
    else if j.val = q + 2 then Sum.inr ()
    else Sum.inl (Sum.inr (jPred q j))

private lemma finToSlot_slotToFin (q : ℕ) (x : (Unit ⊕ Fin (q + 1)) ⊕ Unit) :
    finToSlot q (slotToFin q x) = x := by
  rcases x with (⟨⟨⟩⟩ | i) | ⟨⟩
  · show finToSlot q (⟨0, by omega⟩ : Fin ((q + 1) + 2)) = _
    unfold finToSlot; rw [if_pos rfl]
  · show finToSlot q (⟨i.val + 1, by have := i.isLt; omega⟩ : Fin ((q + 1) + 2)) = _
    unfold finToSlot
    rw [if_neg (show i.val + 1 ≠ 0 by omega),
        if_neg (show i.val + 1 ≠ q + 2 by have := i.isLt; omega)]
    show Sum.inl (Sum.inr (jPred q _)) = Sum.inl (Sum.inr i)
    congr 1; congr 1
    apply Fin.eq_of_val_eq
    show (i.val + 1 - 1) % (q + 1) = i.val
    have hmod : i.val + 1 - 1 = i.val := by omega
    rw [hmod, Nat.mod_eq_of_lt i.isLt]
  · show finToSlot q (⟨q + 2, by omega⟩ : Fin ((q + 1) + 2)) = _
    unfold finToSlot
    rw [if_neg (show q + 2 ≠ 0 by omega), if_pos rfl]

private lemma slotToFin_finToSlot (q : ℕ) (j : Fin ((q + 1) + 2)) :
    slotToFin q (finToSlot q j) = j := by
  unfold finToSlot
  by_cases h0 : j.val = 0
  · rw [if_pos h0]
    show (⟨0, _⟩ : Fin _) = j
    exact Fin.eq_of_val_eq h0.symm
  · rw [if_neg h0]
    by_cases hT : j.val = q + 2
    · rw [if_pos hT]
      show (⟨q + 2, _⟩ : Fin _) = j
      exact Fin.eq_of_val_eq hT.symm
    · rw [if_neg hT]
      show (⟨_ + 1, _⟩ : Fin _) = j
      apply Fin.eq_of_val_eq
      show (j.val - 1) % (q + 1) + 1 = j.val
      have hjlt : j.val < q + 3 := j.isLt
      have hbnd : j.val - 1 < q + 1 := by omega
      rw [Nat.mod_eq_of_lt hbnd]; omega

private def slotEquiv (q : ℕ) : (Unit ⊕ Fin (q + 1)) ⊕ Unit ≃ Fin ((q + 1) + 2) where
  toFun := slotToFin q
  invFun := finToSlot q
  left_inv := finToSlot_slotToFin q
  right_inv := slotToFin_finToSlot q

private lemma vfun_comp (q : ℕ) (γ : K) :
    vfun (K := K) q γ (slotEquiv q (Sum.inl (Sum.inl ()))) = polyComp q γ := by
  funext s
  show vfun q γ (⟨0, by omega⟩ : Fin ((q + 1) + 2)) s = _
  unfold vfun
  rw [dif_pos rfl]

private lemma vfun_mid (q : ℕ) (γ : K) (i : Fin (q + 1)) :
    vfun (K := K) q γ (slotEquiv q (Sum.inl (Sum.inr i))) = polyMid q i := by
  funext s
  show vfun q γ (⟨i.val + 1, by have := i.isLt; omega⟩ : Fin ((q + 1) + 2)) s = _
  unfold vfun
  rw [dif_neg (show i.val + 1 ≠ 0 by omega),
      dif_neg (show i.val + 1 ≠ q + 2 by have := i.isLt; omega)]
  show polyMid q ⟨i.val + 1 - 1, _⟩ s = polyMid q i s
  have : (⟨i.val + 1 - 1, by have := i.isLt; omega⟩ : Fin (q+1)) = i := by
    apply Fin.eq_of_val_eq; show i.val + 1 - 1 = i.val; omega
  rw [this]

private lemma vfun_bdry (q : ℕ) (γ : K) :
    vfun (K := K) q γ (slotEquiv q (Sum.inr ())) = polyBdry q γ := by
  funext s
  show vfun q γ (⟨q + 2, by omega⟩ : Fin ((q + 1) + 2)) s = _
  unfold vfun
  rw [dif_neg (show q + 2 ≠ 0 by omega), dif_pos rfl]

private lemma Phi_coeff_split (q : ℕ) (γ : K) (k : ℕ) :
    (Phi (K := K) q γ).coeff k =
      ((Finset.Nat.antidiagonalTuple 3 k).sum
        (fun m => tprod K (fun i => (polyComp q γ i) (m i)))) +
      (∑ i : Fin (q + 1), (Finset.Nat.antidiagonalTuple 3 k).sum
        (fun m => tprod K (fun s => (polyMid q i s) (m s)))) +
      ((Finset.Nat.antidiagonalTuple 3 k).sum
        (fun m => tprod K (fun i => (polyBdry q γ i) (m i)))) := by
  rw [Phi_coeff_expand]
  rw [← Equiv.sum_comp (slotEquiv q) (fun j => (Finset.Nat.antidiagonalTuple 3 k).sum
    (fun m => tprod K (fun i => (vfun (K := K) q γ j i) (m i))))]
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  have hcomp : (∑ u : Unit, (Finset.Nat.antidiagonalTuple 3 k).sum
      (fun m => tprod K (fun i =>
        (vfun (K := K) q γ (slotEquiv q (Sum.inl (Sum.inl u))) i) (m i)))) =
      (Finset.Nat.antidiagonalTuple 3 k).sum
        (fun m => tprod K (fun i => (polyComp (K := K) q γ i) (m i))) := by
    rw [Finset.univ_unique]
    simp only [Finset.sum_singleton]
    rw [vfun_comp]
  have hbdry : (∑ u : Unit, (Finset.Nat.antidiagonalTuple 3 k).sum
      (fun m => tprod K (fun i =>
        (vfun (K := K) q γ (slotEquiv q (Sum.inr u)) i) (m i)))) =
      (Finset.Nat.antidiagonalTuple 3 k).sum
        (fun m => tprod K (fun i => (polyBdry (K := K) q γ i) (m i))) := by
    rw [Finset.univ_unique]
    simp only [Finset.sum_singleton]
    rw [vfun_bdry]
  rw [hcomp, hbdry]
  have hmid : (∑ i : Fin (q + 1), (Finset.Nat.antidiagonalTuple 3 k).sum
      (fun m => tprod K (fun s =>
        (vfun (K := K) q γ (slotEquiv q (Sum.inl (Sum.inr i))) s) (m s)))) =
      (∑ i : Fin (q + 1), (Finset.Nat.antidiagonalTuple 3 k).sum
        (fun m => tprod K (fun s => (polyMid (K := K) q i s) (m s)))) := by
    apply Finset.sum_congr rfl
    intro i _
    have hf : vfun (K := K) q γ (slotEquiv q (Sum.inl (Sum.inr i))) = polyMid q i :=
      vfun_mid q γ i
    rw [hf]
  rw [hmid]

/-! ## Evaluation lemmas -/

private lemma polyMid_eval0 (q : ℕ) (i : Fin (q + 1)) (s : Fin 3) :
    (polyMid (K := K) q i s) 0 = eO (K := K) (q + 1) s := by
  unfold polyMid
  rw [Finsupp.add_apply, Finsupp.single_eq_same, Finsupp.single_apply, if_neg (by omega)]
  exact AddMonoid.add_zero _

private lemma polyMid_eval1 (q : ℕ) (i : Fin (q + 1)) (s : Fin 3) :
    (polyMid (K := K) q i s) 1 = eM (K := K) q i s := by
  unfold polyMid
  rw [Finsupp.add_apply, Finsupp.single_apply, if_neg (by omega), Finsupp.single_eq_same]
  exact AddMonoid.zero_add _

private lemma polyMid_eval_ge2 (q : ℕ) (i : Fin (q + 1)) (s : Fin 3) {k : ℕ}
    (hk : 2 ≤ k) : (polyMid (K := K) q i s) k = 0 := by
  unfold polyMid
  rw [Finsupp.add_apply, Finsupp.single_apply, if_neg (by omega),
      Finsupp.single_apply, if_neg (by omega)]
  exact AddMonoid.add_zero _

private lemma polyBdry_eval0 (q : ℕ) (γ : K) (s : Fin 3) :
    (polyBdry (K := K) q γ s) 0 = eO (K := K) (q + 1) s := by
  unfold polyBdry
  rw [Finsupp.add_apply, Finsupp.add_apply, Finsupp.single_eq_same,
      Finsupp.single_apply, if_neg (by omega), Finsupp.single_apply, if_neg (by omega)]
  rw [AddMonoid.add_zero, AddMonoid.add_zero]

private lemma polyBdry_eval1 (q : ℕ) (γ : K) (s : Fin 3) :
    (polyBdry (K := K) q γ s) 1 = γ • E (K := K) q s := by
  unfold polyBdry
  rw [Finsupp.add_apply, Finsupp.add_apply, Finsupp.single_apply, if_neg (by omega),
      Finsupp.single_eq_same, Finsupp.single_apply, if_neg (by omega)]
  rw [AddMonoid.zero_add, AddMonoid.add_zero]

private lemma polyBdry_eval2 (q : ℕ) (γ : K) (s : Fin 3) :
    (polyBdry (K := K) q γ s) 2 = eT (K := K) (q + 1) s := by
  unfold polyBdry
  rw [Finsupp.add_apply, Finsupp.add_apply, Finsupp.single_apply, if_neg (by omega),
      Finsupp.single_apply, if_neg (by omega), Finsupp.single_eq_same]
  rw [AddMonoid.zero_add, AddMonoid.zero_add]

private lemma polyBdry_eval_ge3 (q : ℕ) (γ : K) (s : Fin 3) {k : ℕ} (hk : 3 ≤ k) :
    (polyBdry (K := K) q γ s) k = 0 := by
  unfold polyBdry
  rw [Finsupp.add_apply, Finsupp.add_apply, Finsupp.single_apply, if_neg (by omega),
      Finsupp.single_apply, if_neg (by omega), Finsupp.single_apply, if_neg (by omega)]
  rw [AddMonoid.add_zero, AddMonoid.add_zero]

private lemma polyComp_eval0_mode0 (q : ℕ) (γ : K) :
    (polyComp (K := K) q γ ⟨0, by omega⟩) 0 =
      -((q + 2 : K)) • eO (K := K) (q + 1) ⟨0, by omega⟩ := by
  unfold polyComp
  rw [Finsupp.add_apply, Finsupp.single_eq_same,
      Finsupp.single_eq_of_ne' (by omega : (1 : ℕ) ≠ 0), add_zero]
  show (if (0 : ℕ) = 0 then _ else _) = _
  rw [if_pos rfl]

private lemma polyComp_eval0_mode1 (q : ℕ) (γ : K) :
    (polyComp (K := K) q γ ⟨1, by omega⟩) 0 = eO (K := K) (q + 1) ⟨1, by omega⟩ := by
  unfold polyComp
  rw [Finsupp.add_apply, Finsupp.single_eq_same,
      Finsupp.single_eq_of_ne' (by omega : (1 : ℕ) ≠ 0), add_zero]
  show (if (1 : ℕ) = 0 then _ else _) = _
  rw [if_neg (by decide : ¬ (1 : ℕ) = 0)]

private lemma polyComp_eval0_mode2 (q : ℕ) (γ : K) :
    (polyComp (K := K) q γ ⟨2, by omega⟩) 0 = eO (K := K) (q + 1) ⟨2, by omega⟩ := by
  unfold polyComp
  rw [Finsupp.add_apply, Finsupp.single_eq_same,
      Finsupp.single_eq_of_ne' (by omega : (1 : ℕ) ≠ 0), add_zero]
  show (if (2 : ℕ) = 0 then _ else _) = _
  rw [if_neg (by decide : ¬ (2 : ℕ) = 0)]

private lemma polyComp_eval1_mode0 (q : ℕ) (γ : K) :
    (polyComp (K := K) q γ ⟨0, by omega⟩) 1 = -((1 + γ) • E (K := K) q ⟨0, by omega⟩) := by
  unfold polyComp
  rw [Finsupp.add_apply, Finsupp.single_eq_of_ne' (by omega : (0 : ℕ) ≠ 1),
      Finsupp.single_eq_same, zero_add]
  show (if (0 : ℕ) = 0 then _ else _) = _
  rw [if_pos rfl]

private lemma polyComp_eval1_mode1 (q : ℕ) (γ : K) :
    (polyComp (K := K) q γ ⟨1, by omega⟩) 1 =
      ((1 + γ) / (q + 2 : K)) • E (K := K) q ⟨1, by omega⟩ := by
  unfold polyComp
  rw [Finsupp.add_apply, Finsupp.single_eq_of_ne' (by omega : (0 : ℕ) ≠ 1),
      Finsupp.single_eq_same, zero_add]
  show (if (1 : ℕ) = 0 then _ else _) = _
  rw [if_neg (by decide : ¬ (1 : ℕ) = 0)]

private lemma polyComp_eval1_mode2 (q : ℕ) (γ : K) :
    (polyComp (K := K) q γ ⟨2, by omega⟩) 1 =
      ((1 + γ) / (q + 2 : K)) • E (K := K) q ⟨2, by omega⟩ := by
  unfold polyComp
  rw [Finsupp.add_apply, Finsupp.single_eq_of_ne' (by omega : (0 : ℕ) ≠ 1),
      Finsupp.single_eq_same, zero_add]
  show (if (2 : ℕ) = 0 then _ else _) = _
  rw [if_neg (by decide : ¬ (2 : ℕ) = 0)]

private lemma polyComp_eval_ge2 (q : ℕ) (γ : K) (s : Fin 3) {k : ℕ} (hk : 2 ≤ k) :
    (polyComp (K := K) q γ s) k = 0 := by
  unfold polyComp
  rw [Finsupp.add_apply, Finsupp.single_apply, if_neg (by omega),
      Finsupp.single_apply, if_neg (by omega)]
  exact AddMonoid.add_zero _

/-! ## Antidiagonal helpers -/

private lemma antidiagonalTuple_3_1_eq :
    Finset.Nat.antidiagonalTuple 3 1 =
      {![1, 0, 0], ![0, 1, 0], ![0, 0, 1]} := by
  decide

private lemma antidiagonalTuple_3_2_eq :
    Finset.Nat.antidiagonalTuple 3 2 =
      {![2, 0, 0], ![0, 2, 0], ![0, 0, 2], ![1, 1, 0], ![1, 0, 1], ![0, 1, 1]} := by
  decide

/-! ## Order 0 -/

private lemma tprod_update_smul0 (q : ℕ) (c : K) (f : ∀ s : Fin 3, V (K := K) (q+1) s) :
    tprod K (Function.update f ⟨0, by omega⟩ (c • f ⟨0, by omega⟩)) =
      c • tprod K f := by
  rw [(PiTensorProduct.tprod K).map_update_smul, Function.update_eq_self]

private lemma Phi_coeff_zero (q : ℕ) (γ : K) : (Phi (K := K) q γ).coeff 0 = 0 := by
  rw [Phi_coeff_split]
  simp only [Finset.Nat.antidiagonalTuple_zero_right, Finset.sum_singleton, Pi.zero_apply]
  set f0 : ∀ s : Fin 3, V (K := K) (q + 1) s := fun s => eO (K := K) (q + 1) s with hf0_def
  have hcomp : tprod K (fun i => (polyComp (K := K) q γ i) 0) =
      -((q + 2 : K)) • tprod K f0 := by
    have heq : (fun i => (polyComp (K := K) q γ i) 0) =
        Function.update f0 ⟨0, by omega⟩ (-((q + 2 : K)) • f0 ⟨0, by omega⟩) := by
      funext s; fin_cases s
      · rw [polyComp_eval0_mode0, Function.update_self]
      · rw [polyComp_eval0_mode1, Function.update_of_ne (by decide)]
      · rw [polyComp_eval0_mode2, Function.update_of_ne (by decide)]
    rw [heq, tprod_update_smul0]
  have hmid : ∀ i : Fin (q + 1),
      tprod K (fun s => (polyMid (K := K) q i s) 0) = tprod K f0 := by
    intro i
    have heq : (fun s => (polyMid (K := K) q i s) 0) = f0 := by
      funext s; exact polyMid_eval0 q i s
    rw [heq]
  have hbdry : tprod K (fun i => (polyBdry (K := K) q γ i) 0) = tprod K f0 := by
    have heq : (fun i => (polyBdry (K := K) q γ i) 0) = f0 := by
      funext s; exact polyBdry_eval0 q γ s
    rw [heq]
  rw [hcomp, hbdry]
  rw [show (∑ i : Fin (q + 1),
        tprod K (fun s => (polyMid (K := K) q i s) 0)) =
      (q + 1 : ℕ) • tprod K f0 from by
    simp_rw [hmid, Finset.sum_const, Finset.card_univ, Fintype.card_fin]]
  rw [show ((q + 1 : ℕ) : ℕ) • tprod K f0 = ((q + 1 : ℕ) : K) • tprod K f0 from
    (Nat.cast_smul_eq_nsmul K (q+1) (tprod K f0)).symm]
  rw [show ((-((q + 2 : K))) • tprod K f0 + ((q + 1 : ℕ) : K) • tprod K f0 + tprod K f0
        : PiTensorProduct K (CWSpace K (q + 1))) =
      (-((q + 2 : K)) + ((q + 1 : ℕ) : K) + 1) • tprod K f0
    from by rw [add_smul, add_smul, one_smul]]
  have h1 : -((q + 2 : K)) + ((q + 1 : ℕ) : K) + 1 = 0 := by push_cast; ring
  rw [h1, zero_smul]

/-! ## Order 1 -/

private lemma tprod_update_smul_aux (q : ℕ) (i : Fin 3) (c : K)
    (v : V (K := K) (q+1) i) :
    tprod K (Function.update (fun s => eO (K := K) (q + 1) s) i (c • v)) =
      c • tprod K (Function.update (fun s => eO (K := K) (q + 1) s) i v) := by
  set f1 := Function.update (fun s : Fin 3 => eO (K := K) (q + 1) s) i v with hf1
  have h1 : f1 i = v := Function.update_self _ _ _
  have hupd : Function.update (fun s => eO (K := K) (q + 1) s) i (c • v) =
      Function.update f1 i (c • f1 i) := by
    rw [h1, Function.update_idem]
  rw [hupd, (PiTensorProduct.tprod K).map_update_smul, Function.update_eq_self]

private lemma mid_sum_at_degree_one (q : ℕ) (mode : Fin 3) :
    (∑ i : Fin (q + 1),
      tprod K (Function.update (fun s => eO (K := K) (q + 1) s) mode
        (eM (K := K) q i mode))) =
    tprod K (Function.update (fun s => eO (K := K) (q + 1) s) mode (E (K := K) q mode)) := by
  rw [← (PiTensorProduct.tprod K).map_update_sum Finset.univ mode (fun i => eM (K := K) q i mode)
    (fun s => eO (K := K) (q + 1) s)]
  congr 2
  fin_cases mode <;> rfl

private lemma sum_over_antidiag_one {α : Type*} [AddCommMonoid α] (f : (Fin 3 → ℕ) → α) :
    (Finset.Nat.antidiagonalTuple 3 1).sum f = f ![1, 0, 0] + f ![0, 1, 0] + f ![0, 0, 1] := by
  rw [antidiagonalTuple_3_1_eq]
  rw [show ({![1, 0, 0], ![0, 1, 0], ![0, 0, 1]} : Finset (Fin 3 → ℕ)) =
      insert ![1, 0, 0] (insert ![0, 1, 0] {![0, 0, 1]}) from rfl]
  rw [Finset.sum_insert (by
    rw [Finset.mem_insert, Finset.mem_singleton]
    push Not
    refine ⟨?_, ?_⟩ <;>
      (intro h; have := congr_fun h 0; simp at this))]
  rw [Finset.sum_insert (by
    rw [Finset.mem_singleton]
    intro h; have := congr_fun h 1; simp at this)]
  rw [Finset.sum_singleton]
  abel

private lemma polyComp_tprod_eval_100 (q : ℕ) (γ : K) (hQ : (q + 2 : K) ≠ 0) :
    tprod K (fun s : Fin 3 => (polyComp (K := K) q γ s) ((![1, 0, 0] : Fin 3 → ℕ) s)) =
      -((1 + γ)) • tprod K (Function.update (fun s => eO (K := K) (q + 1) s)
        ⟨0, by omega⟩ (E (K := K) q ⟨0, by omega⟩)) := by
  have hf : (fun s : Fin 3 => (polyComp (K := K) q γ s) ((![1, 0, 0] : Fin 3 → ℕ) s)) =
      Function.update (fun s => eO (K := K) (q + 1) s) ⟨0, by omega⟩
        (-((1 + γ)) • E (K := K) q ⟨0, by omega⟩) := by
    funext s; fin_cases s
    · show (polyComp q γ ⟨0, by omega⟩) 1 = _
      rw [polyComp_eval1_mode0, Function.update_self, neg_smul]
    · show (polyComp q γ ⟨1, by omega⟩) 0 = _
      rw [polyComp_eval0_mode1, Function.update_of_ne (by decide)]
    · show (polyComp q γ ⟨2, by omega⟩) 0 = _
      rw [polyComp_eval0_mode2, Function.update_of_ne (by decide)]
  rw [hf, tprod_update_smul_aux]

private lemma tprod_pull_two_smul (q : ℕ) (i j : Fin 3) (hij : i ≠ j) (c d : K)
    (vi : V (K := K) (q + 1) i) (vj : V (K := K) (q + 1) j) :
    tprod K (Function.update
      (Function.update (fun s => eO (K := K) (q + 1) s) i (c • vi)) j (d • vj)) =
    (c * d) • tprod K (Function.update
      (Function.update (fun s => eO (K := K) (q + 1) s) i vi) j vj) := by
  set f0 : ∀ s, V (K := K) (q + 1) s := fun s => eO (K := K) (q + 1) s with hf0
  set g : ∀ s, V (K := K) (q + 1) s := Function.update (Function.update f0 i vi) j vj with hg
  have hgi : g i = vi := by
    show Function.update (Function.update f0 i vi) j vj i = vi
    rw [Function.update_of_ne hij]
    exact Function.update_self _ _ _
  have hgj : g j = vj := by
    show Function.update (Function.update f0 i vi) j vj j = vj
    exact Function.update_self _ _ _
  have hupd : Function.update (Function.update f0 i (c • vi)) j (d • vj) =
      Function.update (Function.update g i (c • g i)) j (d • g j) := by
    funext s
    by_cases hsj : s = j
    · subst hsj
      rw [Function.update_self, Function.update_self, hgj]
    · rw [Function.update_of_ne hsj, Function.update_of_ne hsj]
      by_cases hsi : s = i
      · subst hsi
        rw [Function.update_self, Function.update_self, hgi]
      · rw [Function.update_of_ne hsi, Function.update_of_ne hsi]
        rw [hg, Function.update_of_ne hsj, Function.update_of_ne hsi]
  rw [hupd, (PiTensorProduct.tprod K).map_update_smul]
  have hg_self : Function.update (Function.update g i (c • g i)) j (g j) =
      Function.update g i (c • g i) := by
    funext s
    by_cases hsj : s = j
    · subst hsj
      rw [Function.update_self]
      exact (Function.update_of_ne (Ne.symm hij) _ _).symm
    · rw [Function.update_of_ne hsj]
  rw [hg_self]
  rw [(PiTensorProduct.tprod K).map_update_smul, Function.update_eq_self]
  rw [smul_smul, mul_comm c d]

private lemma polyComp_tprod_eval_010 (q : ℕ) (γ : K) (hQ : (q + 2 : K) ≠ 0) :
    tprod K (fun s : Fin 3 => (polyComp (K := K) q γ s) ((![0, 1, 0] : Fin 3 → ℕ) s)) =
      -((1 + γ)) • tprod K (Function.update (fun s => eO (K := K) (q + 1) s)
        ⟨1, by omega⟩ (E (K := K) q ⟨1, by omega⟩)) := by
  have hf : (fun s : Fin 3 => (polyComp (K := K) q γ s) ((![0, 1, 0] : Fin 3 → ℕ) s)) =
      Function.update (Function.update (fun s => eO (K := K) (q + 1) s)
        (⟨0, by omega⟩ : Fin 3)
        ((-((q + 2 : K))) • eO (K := K) (q + 1) ⟨0, by omega⟩))
        ⟨1, by omega⟩ (((1 + γ) / (q + 2 : K)) • E (K := K) q ⟨1, by omega⟩) := by
    funext s; fin_cases s
    · show (polyComp q γ ⟨0, by omega⟩) 0 = _
      rw [polyComp_eval0_mode0, Function.update_of_ne (by decide), Function.update_self]
    · show (polyComp q γ ⟨1, by omega⟩) 1 = _
      rw [polyComp_eval1_mode1, Function.update_self]
    · show (polyComp q γ ⟨2, by omega⟩) 0 = _
      rw [polyComp_eval0_mode2, Function.update_of_ne (by decide),
          Function.update_of_ne (by decide)]
  rw [hf]
  rw [tprod_pull_two_smul q ⟨0, by omega⟩ ⟨1, by omega⟩ (by decide)]
  rw [show Function.update (Function.update (fun s => eO (K := K) (q + 1) s)
        (⟨0, by omega⟩ : Fin 3) (eO (K := K) (q + 1) ⟨0, by omega⟩))
        ⟨1, by omega⟩ (E (K := K) q ⟨1, by omega⟩) =
      Function.update (fun s => eO (K := K) (q + 1) s)
        (⟨1, by omega⟩ : Fin 3) (E (K := K) q ⟨1, by omega⟩) from by
    rw [Function.update_eq_self]]
  congr 1
  field_simp

private lemma polyComp_tprod_eval_001 (q : ℕ) (γ : K) (hQ : (q + 2 : K) ≠ 0) :
    tprod K (fun s : Fin 3 => (polyComp (K := K) q γ s) ((![0, 0, 1] : Fin 3 → ℕ) s)) =
      -((1 + γ)) • tprod K (Function.update (fun s => eO (K := K) (q + 1) s)
        ⟨2, by omega⟩ (E (K := K) q ⟨2, by omega⟩)) := by
  have hf : (fun s : Fin 3 => (polyComp (K := K) q γ s) ((![0, 0, 1] : Fin 3 → ℕ) s)) =
      Function.update (Function.update (fun s => eO (K := K) (q + 1) s)
        (⟨0, by omega⟩ : Fin 3)
        ((-((q + 2 : K))) • eO (K := K) (q + 1) ⟨0, by omega⟩))
        ⟨2, by omega⟩ (((1 + γ) / (q + 2 : K)) • E (K := K) q ⟨2, by omega⟩) := by
    funext s; fin_cases s
    · show (polyComp q γ ⟨0, by omega⟩) 0 = _
      rw [polyComp_eval0_mode0, Function.update_of_ne (by decide), Function.update_self]
    · show (polyComp q γ ⟨1, by omega⟩) 0 = _
      rw [polyComp_eval0_mode1, Function.update_of_ne (by decide),
          Function.update_of_ne (by decide)]
    · show (polyComp q γ ⟨2, by omega⟩) 1 = _
      rw [polyComp_eval1_mode2, Function.update_self]
  rw [hf]
  rw [tprod_pull_two_smul q ⟨0, by omega⟩ ⟨2, by omega⟩ (by decide)]
  rw [show Function.update (Function.update (fun s => eO (K := K) (q + 1) s)
        (⟨0, by omega⟩ : Fin 3) (eO (K := K) (q + 1) ⟨0, by omega⟩))
        ⟨2, by omega⟩ (E (K := K) q ⟨2, by omega⟩) =
      Function.update (fun s => eO (K := K) (q + 1) s)
        (⟨2, by omega⟩ : Fin 3) (E (K := K) q ⟨2, by omega⟩) from by
    rw [Function.update_eq_self]]
  congr 1
  field_simp

private lemma polyBdry_tprod_eval_100 (q : ℕ) (γ : K) :
    tprod K (fun s : Fin 3 => (polyBdry (K := K) q γ s) ((![1, 0, 0] : Fin 3 → ℕ) s)) =
      γ • tprod K (Function.update (fun s => eO (K := K) (q + 1) s)
        ⟨0, by omega⟩ (E (K := K) q ⟨0, by omega⟩)) := by
  have hf : (fun s : Fin 3 => (polyBdry (K := K) q γ s) ((![1, 0, 0] : Fin 3 → ℕ) s)) =
      Function.update (fun s => eO (K := K) (q + 1) s) ⟨0, by omega⟩
        (γ • E (K := K) q ⟨0, by omega⟩) := by
    funext s; fin_cases s
    · show (polyBdry q γ ⟨0, by omega⟩) 1 = _
      rw [polyBdry_eval1, Function.update_self]
    · show (polyBdry q γ ⟨1, by omega⟩) 0 = _
      rw [polyBdry_eval0, Function.update_of_ne (by decide)]
    · show (polyBdry q γ ⟨2, by omega⟩) 0 = _
      rw [polyBdry_eval0, Function.update_of_ne (by decide)]
  rw [hf, tprod_update_smul_aux]

private lemma polyBdry_tprod_eval_010 (q : ℕ) (γ : K) :
    tprod K (fun s : Fin 3 => (polyBdry (K := K) q γ s) ((![0, 1, 0] : Fin 3 → ℕ) s)) =
      γ • tprod K (Function.update (fun s => eO (K := K) (q + 1) s)
        ⟨1, by omega⟩ (E (K := K) q ⟨1, by omega⟩)) := by
  have hf : (fun s : Fin 3 => (polyBdry (K := K) q γ s) ((![0, 1, 0] : Fin 3 → ℕ) s)) =
      Function.update (fun s => eO (K := K) (q + 1) s) ⟨1, by omega⟩
        (γ • E (K := K) q ⟨1, by omega⟩) := by
    funext s; fin_cases s
    · show (polyBdry q γ ⟨0, by omega⟩) 0 = _
      rw [polyBdry_eval0, Function.update_of_ne (by decide)]
    · show (polyBdry q γ ⟨1, by omega⟩) 1 = _
      rw [polyBdry_eval1, Function.update_self]
    · show (polyBdry q γ ⟨2, by omega⟩) 0 = _
      rw [polyBdry_eval0, Function.update_of_ne (by decide)]
  rw [hf]
  rw [show (Function.update (fun s => eO (K := K) (q + 1) s) (⟨1, by omega⟩ : Fin 3)
        (γ • E (K := K) q ⟨1, by omega⟩)) =
      Function.update (Function.update (fun s => eO (K := K) (q + 1) s) ⟨1, by omega⟩
        (E (K := K) q ⟨1, by omega⟩)) ⟨1, by omega⟩
        (γ • Function.update (fun s => eO (K := K) (q + 1) s) ⟨1, by omega⟩
          (E (K := K) q ⟨1, by omega⟩) ⟨1, by omega⟩) from by
    rw [Function.update_idem, Function.update_self]]
  rw [(PiTensorProduct.tprod K).map_update_smul, Function.update_eq_self]

private lemma polyBdry_tprod_eval_001 (q : ℕ) (γ : K) :
    tprod K (fun s : Fin 3 => (polyBdry (K := K) q γ s) ((![0, 0, 1] : Fin 3 → ℕ) s)) =
      γ • tprod K (Function.update (fun s => eO (K := K) (q + 1) s)
        ⟨2, by omega⟩ (E (K := K) q ⟨2, by omega⟩)) := by
  have hf : (fun s : Fin 3 => (polyBdry (K := K) q γ s) ((![0, 0, 1] : Fin 3 → ℕ) s)) =
      Function.update (fun s => eO (K := K) (q + 1) s) ⟨2, by omega⟩
        (γ • E (K := K) q ⟨2, by omega⟩) := by
    funext s; fin_cases s
    · show (polyBdry q γ ⟨0, by omega⟩) 0 = _
      rw [polyBdry_eval0, Function.update_of_ne (by decide)]
    · show (polyBdry q γ ⟨1, by omega⟩) 0 = _
      rw [polyBdry_eval0, Function.update_of_ne (by decide)]
    · show (polyBdry q γ ⟨2, by omega⟩) 1 = _
      rw [polyBdry_eval1, Function.update_self]
  rw [hf]
  rw [show (Function.update (fun s => eO (K := K) (q + 1) s) (⟨2, by omega⟩ : Fin 3)
        (γ • E (K := K) q ⟨2, by omega⟩)) =
      Function.update (Function.update (fun s => eO (K := K) (q + 1) s) ⟨2, by omega⟩
        (E (K := K) q ⟨2, by omega⟩)) ⟨2, by omega⟩
        (γ • Function.update (fun s => eO (K := K) (q + 1) s) ⟨2, by omega⟩
          (E (K := K) q ⟨2, by omega⟩) ⟨2, by omega⟩) from by
    rw [Function.update_idem, Function.update_self]]
  rw [(PiTensorProduct.tprod K).map_update_smul, Function.update_eq_self]

private lemma polyMid_sum_tprod_eval_100 (q : ℕ) :
    (∑ i : Fin (q + 1),
      tprod K (fun s : Fin 3 => (polyMid (K := K) q i s) ((![1, 0, 0] : Fin 3 → ℕ) s))) =
    tprod K (Function.update (fun s => eO (K := K) (q + 1) s) ⟨0, by omega⟩
      (E (K := K) q ⟨0, by omega⟩)) := by
  have hf : ∀ i : Fin (q + 1),
      (fun s : Fin 3 => (polyMid (K := K) q i s) ((![1, 0, 0] : Fin 3 → ℕ) s)) =
      Function.update (fun s => eO (K := K) (q + 1) s) ⟨0, by omega⟩
        (eM (K := K) q i ⟨0, by omega⟩) := by
    intro i; funext s; fin_cases s
    · show (polyMid q i ⟨0, by omega⟩) 1 = _
      rw [polyMid_eval1, Function.update_self]
    · show (polyMid q i ⟨1, by omega⟩) 0 = _
      rw [polyMid_eval0, Function.update_of_ne (by decide)]
    · show (polyMid q i ⟨2, by omega⟩) 0 = _
      rw [polyMid_eval0, Function.update_of_ne (by decide)]
  simp_rw [hf]
  exact mid_sum_at_degree_one q ⟨0, by omega⟩

private lemma polyMid_sum_tprod_eval_010 (q : ℕ) :
    (∑ i : Fin (q + 1),
      tprod K (fun s : Fin 3 => (polyMid (K := K) q i s) ((![0, 1, 0] : Fin 3 → ℕ) s))) =
    tprod K (Function.update (fun s => eO (K := K) (q + 1) s) ⟨1, by omega⟩
      (E (K := K) q ⟨1, by omega⟩)) := by
  have hf : ∀ i : Fin (q + 1),
      (fun s : Fin 3 => (polyMid (K := K) q i s) ((![0, 1, 0] : Fin 3 → ℕ) s)) =
      Function.update (fun s => eO (K := K) (q + 1) s) ⟨1, by omega⟩
        (eM (K := K) q i ⟨1, by omega⟩) := by
    intro i; funext s; fin_cases s
    · show (polyMid q i ⟨0, by omega⟩) 0 = _
      rw [polyMid_eval0, Function.update_of_ne (by decide)]
    · show (polyMid q i ⟨1, by omega⟩) 1 = _
      rw [polyMid_eval1, Function.update_self]
    · show (polyMid q i ⟨2, by omega⟩) 0 = _
      rw [polyMid_eval0, Function.update_of_ne (by decide)]
  simp_rw [hf]
  exact mid_sum_at_degree_one q ⟨1, by omega⟩

private lemma polyMid_sum_tprod_eval_001 (q : ℕ) :
    (∑ i : Fin (q + 1),
      tprod K (fun s : Fin 3 => (polyMid (K := K) q i s) ((![0, 0, 1] : Fin 3 → ℕ) s))) =
    tprod K (Function.update (fun s => eO (K := K) (q + 1) s) ⟨2, by omega⟩
      (E (K := K) q ⟨2, by omega⟩)) := by
  have hf : ∀ i : Fin (q + 1),
      (fun s : Fin 3 => (polyMid (K := K) q i s) ((![0, 0, 1] : Fin 3 → ℕ) s)) =
      Function.update (fun s => eO (K := K) (q + 1) s) ⟨2, by omega⟩
        (eM (K := K) q i ⟨2, by omega⟩) := by
    intro i; funext s; fin_cases s
    · show (polyMid q i ⟨0, by omega⟩) 0 = _
      rw [polyMid_eval0, Function.update_of_ne (by decide)]
    · show (polyMid q i ⟨1, by omega⟩) 0 = _
      rw [polyMid_eval0, Function.update_of_ne (by decide)]
    · show (polyMid q i ⟨2, by omega⟩) 1 = _
      rw [polyMid_eval1, Function.update_self]
  simp_rw [hf]
  exact mid_sum_at_degree_one q ⟨2, by omega⟩

private lemma cancel_one_plus_gamma {q : ℕ}
    (P : PiTensorProduct K (CWSpace K (q + 1))) (γ : K) :
    -(1 + γ) • P + P + γ • P = 0 := by
  rw [show (-(1 + γ) • P + P + γ • P : PiTensorProduct K (CWSpace K (q + 1))) =
      (-(1 + γ) + 1 + γ) • P from by
    rw [add_smul, add_smul, one_smul]]
  have : -(1 + γ) + 1 + γ = (0 : K) := by ring
  rw [this, zero_smul]

private lemma Phi_coeff_one (q : ℕ) (γ : K) (hQ : (q + 2 : K) ≠ 0) :
    (Phi (K := K) q γ).coeff 1 = 0 := by
  rw [Phi_coeff_split]
  rw [sum_over_antidiag_one (fun m => tprod K (fun i => (polyComp (K := K) q γ i) (m i)))]
  rw [sum_over_antidiag_one (fun m => tprod K (fun i => (polyBdry (K := K) q γ i) (m i)))]
  rw [show (∑ i : Fin (q + 1), (Finset.Nat.antidiagonalTuple 3 1).sum
        (fun m => tprod K (fun s => (polyMid (K := K) q i s) (m s)))) =
      ∑ i : Fin (q + 1),
        (tprod K (fun s => (polyMid (K := K) q i s) ((![1, 0, 0] : Fin 3 → ℕ) s)) +
         tprod K (fun s => (polyMid (K := K) q i s) ((![0, 1, 0] : Fin 3 → ℕ) s)) +
         tprod K (fun s => (polyMid (K := K) q i s) ((![0, 0, 1] : Fin 3 → ℕ) s))) from by
    apply Finset.sum_congr rfl
    intro i _
    exact sum_over_antidiag_one _]
  rw [polyComp_tprod_eval_100 q γ hQ, polyComp_tprod_eval_010 q γ hQ,
      polyComp_tprod_eval_001 q γ hQ,
      polyBdry_tprod_eval_100, polyBdry_tprod_eval_010, polyBdry_tprod_eval_001]
  rw [show (∑ i : Fin (q + 1),
      (tprod K (fun s => (polyMid (K := K) q i s) ((![1, 0, 0] : Fin 3 → ℕ) s)) +
       tprod K (fun s => (polyMid (K := K) q i s) ((![0, 1, 0] : Fin 3 → ℕ) s)) +
       tprod K (fun s => (polyMid (K := K) q i s) ((![0, 0, 1] : Fin 3 → ℕ) s)))) =
    (∑ i : Fin (q + 1),
       tprod K (fun s => (polyMid (K := K) q i s) ((![1, 0, 0] : Fin 3 → ℕ) s))) +
    (∑ i : Fin (q + 1),
       tprod K (fun s => (polyMid (K := K) q i s) ((![0, 1, 0] : Fin 3 → ℕ) s))) +
    (∑ i : Fin (q + 1),
       tprod K (fun s => (polyMid (K := K) q i s) ((![0, 0, 1] : Fin 3 → ℕ) s))) from by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]]
  rw [polyMid_sum_tprod_eval_100, polyMid_sum_tprod_eval_010, polyMid_sum_tprod_eval_001]
  set P0 := tprod K (Function.update (fun s : Fin 3 => eO (K := K) (q + 1) s)
    ⟨0, by omega⟩ (E (K := K) q ⟨0, by omega⟩)) with hP0
  set P1 := tprod K (Function.update (fun s : Fin 3 => eO (K := K) (q + 1) s)
    ⟨1, by omega⟩ (E (K := K) q ⟨1, by omega⟩)) with hP1
  set P2 := tprod K (Function.update (fun s : Fin 3 => eO (K := K) (q + 1) s)
    ⟨2, by omega⟩ (E (K := K) q ⟨2, by omega⟩)) with hP2
  have h0 : -(1 + γ) • P0 + P0 + γ • P0 = 0 := cancel_one_plus_gamma P0 γ
  have h1 : -(1 + γ) • P1 + P1 + γ • P1 = 0 := cancel_one_plus_gamma P1 γ
  have h2 : -(1 + γ) • P2 + P2 + γ • P2 = 0 := cancel_one_plus_gamma P2 γ
  have hsum : (-(1 + γ) • P0 + P0 + γ • P0) + (-(1 + γ) • P1 + P1 + γ • P1) +
              (-(1 + γ) • P2 + P2 + γ • P2) = 0 := by rw [h0, h1, h2]; abel
  rw [show ((-(1 + γ) • P0 + -(1 + γ) • P1 + -(1 + γ) • P2) +
            (P0 + P1 + P2) + (γ • P0 + γ • P1 + γ • P2) :
          PiTensorProduct K (CWSpace K (q + 1))) =
        (-(1 + γ) • P0 + P0 + γ • P0) + (-(1 + γ) • P1 + P1 + γ • P1) +
        (-(1 + γ) • P2 + P2 + γ • P2) from by abel]
  exact hsum

/-! ## Order 2 -/

private lemma matrix_cons_ne_of (a b c d e f : ℕ) (h : a ≠ d ∨ b ≠ e ∨ c ≠ f) :
    (![a, b, c] : Fin 3 → ℕ) ≠ ![d, e, f] := by
  intro heq
  rcases h with h0 | h1 | h2
  · have := congr_fun heq 0; simp at this; exact h0 this
  · have := congr_fun heq 1; simp at this; exact h1 this
  · have := congr_fun heq 2; simp at this; exact h2 this

private lemma sum_over_antidiag_two {α : Type*} [AddCommMonoid α] (f : (Fin 3 → ℕ) → α) :
    (Finset.Nat.antidiagonalTuple 3 2).sum f =
      f ![2, 0, 0] + f ![0, 2, 0] + f ![0, 0, 2] +
      f ![1, 1, 0] + f ![1, 0, 1] + f ![0, 1, 1] := by
  rw [antidiagonalTuple_3_2_eq]
  rw [show ({![2, 0, 0], ![0, 2, 0], ![0, 0, 2], ![1, 1, 0], ![1, 0, 1], ![0, 1, 1]}
      : Finset (Fin 3 → ℕ)) =
      insert ![2, 0, 0] (insert ![0, 2, 0] (insert ![0, 0, 2]
        (insert ![1, 1, 0] (insert ![1, 0, 1] {![0, 1, 1]})))) from rfl]
  rw [Finset.sum_insert (by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
      (apply matrix_cons_ne_of; tauto))]
  rw [Finset.sum_insert (by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      (apply matrix_cons_ne_of; tauto))]
  rw [Finset.sum_insert (by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    refine ⟨?_, ?_, ?_⟩ <;>
      (apply matrix_cons_ne_of; tauto))]
  rw [Finset.sum_insert (by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    refine ⟨?_, ?_⟩ <;>
      (apply matrix_cons_ne_of; tauto))]
  rw [Finset.sum_insert (by
    simp only [Finset.mem_singleton]
    apply matrix_cons_ne_of; tauto)]
  rw [Finset.sum_singleton]
  abel

/-! ### polyBdry, polyMid, polyComp at boundary tuples (200, 020, 002) -/

private lemma polyComp_tprod_eval_200 (q : ℕ) (γ : K) :
    tprod K (fun s : Fin 3 => (polyComp (K := K) q γ s) ((![2, 0, 0] : Fin 3 → ℕ) s)) = 0 := by
  apply (PiTensorProduct.tprod K).map_coord_zero ⟨0, by omega⟩
  show (polyComp (K := K) q γ ⟨0, by omega⟩) 2 = 0
  exact polyComp_eval_ge2 q γ _ (by omega)

private lemma polyComp_tprod_eval_020 (q : ℕ) (γ : K) :
    tprod K (fun s : Fin 3 => (polyComp (K := K) q γ s) ((![0, 2, 0] : Fin 3 → ℕ) s)) = 0 := by
  apply (PiTensorProduct.tprod K).map_coord_zero ⟨1, by omega⟩
  show (polyComp (K := K) q γ ⟨1, by omega⟩) 2 = 0
  exact polyComp_eval_ge2 q γ _ (by omega)

private lemma polyComp_tprod_eval_002 (q : ℕ) (γ : K) :
    tprod K (fun s : Fin 3 => (polyComp (K := K) q γ s) ((![0, 0, 2] : Fin 3 → ℕ) s)) = 0 := by
  apply (PiTensorProduct.tprod K).map_coord_zero ⟨2, by omega⟩
  show (polyComp (K := K) q γ ⟨2, by omega⟩) 2 = 0
  exact polyComp_eval_ge2 q γ _ (by omega)

private lemma polyMid_tprod_eval_200 (q : ℕ) (i : Fin (q + 1)) :
    tprod K (fun s : Fin 3 => (polyMid (K := K) q i s) ((![2, 0, 0] : Fin 3 → ℕ) s)) = 0 := by
  apply (PiTensorProduct.tprod K).map_coord_zero ⟨0, by omega⟩
  show (polyMid (K := K) q i ⟨0, by omega⟩) 2 = 0
  exact polyMid_eval_ge2 q i _ (by omega)

private lemma polyMid_tprod_eval_020 (q : ℕ) (i : Fin (q + 1)) :
    tprod K (fun s : Fin 3 => (polyMid (K := K) q i s) ((![0, 2, 0] : Fin 3 → ℕ) s)) = 0 := by
  apply (PiTensorProduct.tprod K).map_coord_zero ⟨1, by omega⟩
  show (polyMid (K := K) q i ⟨1, by omega⟩) 2 = 0
  exact polyMid_eval_ge2 q i _ (by omega)

private lemma polyMid_tprod_eval_002 (q : ℕ) (i : Fin (q + 1)) :
    tprod K (fun s : Fin 3 => (polyMid (K := K) q i s) ((![0, 0, 2] : Fin 3 → ℕ) s)) = 0 := by
  apply (PiTensorProduct.tprod K).map_coord_zero ⟨2, by omega⟩
  show (polyMid (K := K) q i ⟨2, by omega⟩) 2 = 0
  exact polyMid_eval_ge2 q i _ (by omega)

private lemma polyBdry_tprod_eval_200 (q : ℕ) (γ : K) :
    tprod K (fun s : Fin 3 => (polyBdry (K := K) q γ s) ((![2, 0, 0] : Fin 3 → ℕ) s)) =
      CWMonom K (q + 1) (T (q + 1)) (O (q + 1)) (O (q + 1)) := by
  unfold CWMonom
  congr 1; funext s; fin_cases s
  · show (polyBdry (K := K) q γ ⟨0, by omega⟩) 2 = _
    rw [polyBdry_eval2]; rfl
  · show (polyBdry (K := K) q γ ⟨1, by omega⟩) 0 = _
    rw [polyBdry_eval0]; rfl
  · show (polyBdry (K := K) q γ ⟨2, by omega⟩) 0 = _
    rw [polyBdry_eval0]; rfl

private lemma polyBdry_tprod_eval_020 (q : ℕ) (γ : K) :
    tprod K (fun s : Fin 3 => (polyBdry (K := K) q γ s) ((![0, 2, 0] : Fin 3 → ℕ) s)) =
      CWMonom K (q + 1) (O (q + 1)) (T (q + 1)) (O (q + 1)) := by
  unfold CWMonom
  congr 1; funext s; fin_cases s
  · show (polyBdry (K := K) q γ ⟨0, by omega⟩) 0 = _
    rw [polyBdry_eval0]; rfl
  · show (polyBdry (K := K) q γ ⟨1, by omega⟩) 2 = _
    rw [polyBdry_eval2]; rfl
  · show (polyBdry (K := K) q γ ⟨2, by omega⟩) 0 = _
    rw [polyBdry_eval0]; rfl

private lemma polyBdry_tprod_eval_002 (q : ℕ) (γ : K) :
    tprod K (fun s : Fin 3 => (polyBdry (K := K) q γ s) ((![0, 0, 2] : Fin 3 → ℕ) s)) =
      CWMonom K (q + 1) (O (q + 1)) (O (q + 1)) (T (q + 1)) := by
  unfold CWMonom
  congr 1; funext s; fin_cases s
  · show (polyBdry (K := K) q γ ⟨0, by omega⟩) 0 = _
    rw [polyBdry_eval0]; rfl
  · show (polyBdry (K := K) q γ ⟨1, by omega⟩) 0 = _
    rw [polyBdry_eval0]; rfl
  · show (polyBdry (K := K) q γ ⟨2, by omega⟩) 2 = _
    rw [polyBdry_eval2]; rfl

/-! ### Cross-tuple pure tensors: `E` at two modes, `eO` at the third -/

private noncomputable def pureEE_O (q : ℕ) : PiTensorProduct K (CWSpace K (q + 1)) :=
  tprod K (fun s : Fin 3 => match s with
    | ⟨0, _⟩ => E (K := K) q ⟨0, by omega⟩
    | ⟨1, _⟩ => E (K := K) q ⟨1, by omega⟩
    | ⟨2, _⟩ => eO (K := K) (q + 1) ⟨2, by omega⟩)

private noncomputable def pureE_OE (q : ℕ) : PiTensorProduct K (CWSpace K (q + 1)) :=
  tprod K (fun s : Fin 3 => match s with
    | ⟨0, _⟩ => E (K := K) q ⟨0, by omega⟩
    | ⟨1, _⟩ => eO (K := K) (q + 1) ⟨1, by omega⟩
    | ⟨2, _⟩ => E (K := K) q ⟨2, by omega⟩)

private noncomputable def pureO_EE (q : ℕ) : PiTensorProduct K (CWSpace K (q + 1)) :=
  tprod K (fun s : Fin 3 => match s with
    | ⟨0, _⟩ => eO (K := K) (q + 1) ⟨0, by omega⟩
    | ⟨1, _⟩ => E (K := K) q ⟨1, by omega⟩
    | ⟨2, _⟩ => E (K := K) q ⟨2, by omega⟩)

/-- Pull scalars from two distinct modes of a 3-tprod (general version). -/
private lemma tprod_pull_two_smul_general (q : ℕ) (i j : Fin 3) (hij : i ≠ j)
    (c d : K) (f : ∀ s : Fin 3, V (K := K) (q + 1) s)
    (vi : V (K := K) (q + 1) i) (vj : V (K := K) (q + 1) j) :
    tprod K (Function.update (Function.update f i (c • vi)) j (d • vj)) =
    (c * d) • tprod K (Function.update (Function.update f i vi) j vj) := by
  set g : ∀ s, V (K := K) (q + 1) s := Function.update (Function.update f i vi) j vj with hg
  have hgi : g i = vi := by
    show Function.update (Function.update f i vi) j vj i = vi
    rw [Function.update_of_ne hij]
    exact Function.update_self _ _ _
  have hgj : g j = vj := by
    show Function.update (Function.update f i vi) j vj j = vj
    exact Function.update_self _ _ _
  have hupd : Function.update (Function.update f i (c • vi)) j (d • vj) =
      Function.update (Function.update g i (c • g i)) j (d • g j) := by
    funext s
    by_cases hsj : s = j
    · subst hsj
      rw [Function.update_self, Function.update_self, hgj]
    · rw [Function.update_of_ne hsj, Function.update_of_ne hsj]
      by_cases hsi : s = i
      · subst hsi
        rw [Function.update_self, Function.update_self, hgi]
      · rw [Function.update_of_ne hsi, Function.update_of_ne hsi]
        rw [hg, Function.update_of_ne hsj, Function.update_of_ne hsi]
  rw [hupd, (PiTensorProduct.tprod K).map_update_smul]
  have hg_self : Function.update (Function.update g i (c • g i)) j (g j) =
      Function.update g i (c • g i) := by
    funext s
    by_cases hsj : s = j
    · subst hsj
      rw [Function.update_self]
      exact (Function.update_of_ne (Ne.symm hij) _ _).symm
    · rw [Function.update_of_ne hsj]
  rw [hg_self]
  rw [(PiTensorProduct.tprod K).map_update_smul, Function.update_eq_self]
  rw [smul_smul, mul_comm c d]

/-! ### polyComp at cross tuples (1,1,0), (1,0,1), (0,1,1) -/

private lemma polyComp_tprod_eval_110 (q : ℕ) (γ : K) (hQ : (q + 2 : K) ≠ 0) :
    tprod K (fun s : Fin 3 => (polyComp (K := K) q γ s) ((![1, 1, 0] : Fin 3 → ℕ) s)) =
      (-(1 + γ) * ((1 + γ) / (q + 2 : K))) • pureEE_O q := by
  have hf : (fun s : Fin 3 => (polyComp (K := K) q γ s) ((![1, 1, 0] : Fin 3 → ℕ) s)) =
      Function.update (Function.update (fun s : Fin 3 => eO (K := K) (q + 1) s)
        (⟨0, by omega⟩ : Fin 3) ((-(1 + γ)) • E (K := K) q ⟨0, by omega⟩))
        (⟨1, by omega⟩ : Fin 3) (((1 + γ) / (q + 2 : K)) • E (K := K) q ⟨1, by omega⟩) := by
    funext s; fin_cases s
    · show (polyComp q γ ⟨0, by omega⟩) 1 = _
      rw [polyComp_eval1_mode0, Function.update_of_ne (by decide), Function.update_self, neg_smul]
    · show (polyComp q γ ⟨1, by omega⟩) 1 = _
      rw [polyComp_eval1_mode1, Function.update_self]
    · show (polyComp q γ ⟨2, by omega⟩) 0 = _
      rw [polyComp_eval0_mode2, Function.update_of_ne (by decide), Function.update_of_ne (by decide)]
  rw [hf]
  rw [tprod_pull_two_smul_general q ⟨0, by omega⟩ ⟨1, by omega⟩ (by decide)]
  congr 1
  show tprod K _ = pureEE_O q
  unfold pureEE_O
  congr 1; funext s; fin_cases s
  · show Function.update (Function.update _ (⟨0, by omega⟩ : Fin 3) _)
      (⟨1, by omega⟩ : Fin 3) _ ⟨0, by omega⟩ = _
    rw [Function.update_of_ne (by decide), Function.update_self]
  · show Function.update (Function.update _ (⟨0, by omega⟩ : Fin 3) _)
      (⟨1, by omega⟩ : Fin 3) _ ⟨1, by omega⟩ = _
    rw [Function.update_self]
  · show Function.update (Function.update _ (⟨0, by omega⟩ : Fin 3) _)
      (⟨1, by omega⟩ : Fin 3) _ ⟨2, by omega⟩ = _
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]

private lemma polyComp_tprod_eval_101 (q : ℕ) (γ : K) (hQ : (q + 2 : K) ≠ 0) :
    tprod K (fun s : Fin 3 => (polyComp (K := K) q γ s) ((![1, 0, 1] : Fin 3 → ℕ) s)) =
      (-(1 + γ) * ((1 + γ) / (q + 2 : K))) • pureE_OE q := by
  have hf : (fun s : Fin 3 => (polyComp (K := K) q γ s) ((![1, 0, 1] : Fin 3 → ℕ) s)) =
      Function.update (Function.update (fun s : Fin 3 => eO (K := K) (q + 1) s)
        (⟨0, by omega⟩ : Fin 3) ((-(1 + γ)) • E (K := K) q ⟨0, by omega⟩))
        (⟨2, by omega⟩ : Fin 3) (((1 + γ) / (q + 2 : K)) • E (K := K) q ⟨2, by omega⟩) := by
    funext s; fin_cases s
    · show (polyComp q γ ⟨0, by omega⟩) 1 = _
      rw [polyComp_eval1_mode0, Function.update_of_ne (by decide), Function.update_self, neg_smul]
    · show (polyComp q γ ⟨1, by omega⟩) 0 = _
      rw [polyComp_eval0_mode1, Function.update_of_ne (by decide), Function.update_of_ne (by decide)]
    · show (polyComp q γ ⟨2, by omega⟩) 1 = _
      rw [polyComp_eval1_mode2, Function.update_self]
  rw [hf]
  rw [tprod_pull_two_smul_general q ⟨0, by omega⟩ ⟨2, by omega⟩ (by decide)]
  congr 1
  show tprod K _ = pureE_OE q
  unfold pureE_OE
  congr 1; funext s; fin_cases s
  · show Function.update (Function.update _ (⟨0, by omega⟩ : Fin 3) _)
      (⟨2, by omega⟩ : Fin 3) _ ⟨0, by omega⟩ = _
    rw [Function.update_of_ne (by decide), Function.update_self]
  · show Function.update (Function.update _ (⟨0, by omega⟩ : Fin 3) _)
      (⟨2, by omega⟩ : Fin 3) _ ⟨1, by omega⟩ = _
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]
  · show Function.update (Function.update _ (⟨0, by omega⟩ : Fin 3) _)
      (⟨2, by omega⟩ : Fin 3) _ ⟨2, by omega⟩ = _
    rw [Function.update_self]

private lemma polyComp_tprod_eval_011 (q : ℕ) (γ : K) (hQ : (q + 2 : K) ≠ 0) :
    tprod K (fun s : Fin 3 => (polyComp (K := K) q γ s) ((![0, 1, 1] : Fin 3 → ℕ) s)) =
      (-(1 + γ) * ((1 + γ) / (q + 2 : K))) • pureO_EE q := by
  have hf : (fun s : Fin 3 => (polyComp (K := K) q γ s) ((![0, 1, 1] : Fin 3 → ℕ) s)) =
      (fun s : Fin 3 => match s with
        | ⟨0, _⟩ => (-((q + 2 : K))) • eO (K := K) (q + 1) ⟨0, by omega⟩
        | ⟨1, _⟩ => ((1 + γ) / (q + 2 : K)) • E (K := K) q ⟨1, by omega⟩
        | ⟨2, _⟩ => ((1 + γ) / (q + 2 : K)) • E (K := K) q ⟨2, by omega⟩) := by
    funext s; fin_cases s
    · show (polyComp q γ ⟨0, by omega⟩) 0 = _
      rw [polyComp_eval0_mode0]
    · show (polyComp q γ ⟨1, by omega⟩) 1 = _
      rw [polyComp_eval1_mode1]
    · show (polyComp q γ ⟨2, by omega⟩) 1 = _
      rw [polyComp_eval1_mode2]
  rw [hf]
  have hupd : (fun s : Fin 3 => match s with
      | ⟨0, _⟩ => (-((q + 2 : K))) • eO (K := K) (q + 1) ⟨0, by omega⟩
      | ⟨1, _⟩ => ((1 + γ) / (q + 2 : K)) • E (K := K) q ⟨1, by omega⟩
      | ⟨2, _⟩ => ((1 + γ) / (q + 2 : K)) • E (K := K) q ⟨2, by omega⟩) =
    Function.update (Function.update (Function.update
      (fun s : Fin 3 => match s with
        | ⟨0, _⟩ => eO (K := K) (q + 1) ⟨0, by omega⟩
        | ⟨1, _⟩ => E (K := K) q ⟨1, by omega⟩
        | ⟨2, _⟩ => E (K := K) q ⟨2, by omega⟩)
      ⟨0, by omega⟩ ((-((q + 2 : K))) • eO (K := K) (q + 1) ⟨0, by omega⟩))
      ⟨1, by omega⟩ (((1 + γ) / (q + 2 : K)) • E (K := K) q ⟨1, by omega⟩))
      ⟨2, by omega⟩ (((1 + γ) / (q + 2 : K)) • E (K := K) q ⟨2, by omega⟩) := by
    funext s; fin_cases s
    · rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          Function.update_self]
    · rw [Function.update_of_ne (by decide), Function.update_self]
    · rw [Function.update_self]
  rw [hupd]
  set base : ∀ s : Fin 3, V (K := K) (q + 1) s := fun s : Fin 3 => match s with
    | ⟨0, _⟩ => eO (K := K) (q + 1) ⟨0, by omega⟩
    | ⟨1, _⟩ => E (K := K) q ⟨1, by omega⟩
    | ⟨2, _⟩ => E (K := K) q ⟨2, by omega⟩
  have hb0 : base ⟨0, by omega⟩ = eO (K := K) (q + 1) ⟨0, by omega⟩ := rfl
  have hb1 : base ⟨1, by omega⟩ = E (K := K) q ⟨1, by omega⟩ := rfl
  have hb2 : base ⟨2, by omega⟩ = E (K := K) q ⟨2, by omega⟩ := rfl
  rw [show (((-((q + 2 : K))) • eO (K := K) (q + 1) ⟨0, by omega⟩) :
      V (K := K) (q + 1) ⟨0, by omega⟩) = (-((q + 2 : K))) • base ⟨0, by omega⟩ from by rw [hb0]]
  rw [show (((1 + γ) / (q + 2 : K)) • E (K := K) q ⟨1, by omega⟩ :
      V (K := K) (q + 1) ⟨1, by omega⟩) = ((1 + γ) / (q + 2 : K)) • base ⟨1, by omega⟩ from by rw [hb1]]
  rw [show (((1 + γ) / (q + 2 : K)) • E (K := K) q ⟨2, by omega⟩ :
      V (K := K) (q + 1) ⟨2, by omega⟩) = ((1 + γ) / (q + 2 : K)) • base ⟨2, by omega⟩ from by rw [hb2]]
  rw [(PiTensorProduct.tprod K).map_update_smul]
  rw [show Function.update (Function.update (Function.update base
        ⟨0, by omega⟩ ((-((q + 2 : K))) • base ⟨0, by omega⟩))
        ⟨1, by omega⟩ (((1 + γ) / (q + 2 : K)) • base ⟨1, by omega⟩))
        ⟨2, by omega⟩ (base ⟨2, by omega⟩) =
      Function.update (Function.update base
        ⟨0, by omega⟩ ((-((q + 2 : K))) • base ⟨0, by omega⟩))
        ⟨1, by omega⟩ (((1 + γ) / (q + 2 : K)) • base ⟨1, by omega⟩) from by
    funext s; by_cases hs2 : s = ⟨2, by omega⟩
    · subst hs2; rw [Function.update_self,
        Function.update_of_ne (by decide), Function.update_of_ne (by decide)]
    · rw [Function.update_of_ne hs2]]
  rw [(PiTensorProduct.tprod K).map_update_smul]
  rw [show Function.update (Function.update base
        ⟨0, by omega⟩ ((-((q + 2 : K))) • base ⟨0, by omega⟩))
        ⟨1, by omega⟩ (base ⟨1, by omega⟩) =
      Function.update base ⟨0, by omega⟩ ((-((q + 2 : K))) • base ⟨0, by omega⟩) from by
    funext s; by_cases hs1 : s = ⟨1, by omega⟩
    · subst hs1; rw [Function.update_self, Function.update_of_ne (by decide)]
    · rw [Function.update_of_ne hs1]]
  rw [(PiTensorProduct.tprod K).map_update_smul, Function.update_eq_self]
  show ((1 + γ) / (q + 2 : K)) • ((1 + γ) / (q + 2 : K)) • (-((q + 2 : K))) • tprod K base =
      (-(1 + γ) * ((1 + γ) / (q + 2 : K))) • pureO_EE q
  rw [smul_smul, smul_smul]
  have hbase : tprod K base = pureO_EE q := rfl
  rw [hbase]
  congr 1
  field_simp

/-! ### polyBdry at cross tuples (1,1,0), (1,0,1), (0,1,1)

`polyBdry s 1 = γ • E s`, so the result is `γ² • pureEE_..`. -/

private lemma polyBdry_tprod_eval_110 (q : ℕ) (γ : K) :
    tprod K (fun s : Fin 3 => (polyBdry (K := K) q γ s) ((![1, 1, 0] : Fin 3 → ℕ) s)) =
      (γ * γ) • pureEE_O q := by
  have hf : (fun s : Fin 3 => (polyBdry (K := K) q γ s) ((![1, 1, 0] : Fin 3 → ℕ) s)) =
      Function.update (Function.update (fun s : Fin 3 => eO (K := K) (q + 1) s)
        (⟨0, by omega⟩ : Fin 3) (γ • E (K := K) q ⟨0, by omega⟩))
        (⟨1, by omega⟩ : Fin 3) (γ • E (K := K) q ⟨1, by omega⟩) := by
    funext s; fin_cases s
    · show (polyBdry q γ ⟨0, by omega⟩) 1 = _
      rw [polyBdry_eval1, Function.update_of_ne (by decide), Function.update_self]
    · show (polyBdry q γ ⟨1, by omega⟩) 1 = _
      rw [polyBdry_eval1, Function.update_self]
    · show (polyBdry q γ ⟨2, by omega⟩) 0 = _
      rw [polyBdry_eval0, Function.update_of_ne (by decide), Function.update_of_ne (by decide)]
  rw [hf]
  rw [tprod_pull_two_smul_general q ⟨0, by omega⟩ ⟨1, by omega⟩ (by decide)]
  show (γ * γ) • tprod K _ = (γ * γ) • pureEE_O q
  congr 1
  show tprod K _ = pureEE_O q
  unfold pureEE_O
  congr 1; funext s; fin_cases s
  · show Function.update (Function.update _ (⟨0, by omega⟩ : Fin 3) _)
      (⟨1, by omega⟩ : Fin 3) _ ⟨0, by omega⟩ = _
    rw [Function.update_of_ne (by decide), Function.update_self]
  · show Function.update (Function.update _ (⟨0, by omega⟩ : Fin 3) _)
      (⟨1, by omega⟩ : Fin 3) _ ⟨1, by omega⟩ = _
    rw [Function.update_self]
  · show Function.update (Function.update _ (⟨0, by omega⟩ : Fin 3) _)
      (⟨1, by omega⟩ : Fin 3) _ ⟨2, by omega⟩ = _
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]

private lemma polyBdry_tprod_eval_101 (q : ℕ) (γ : K) :
    tprod K (fun s : Fin 3 => (polyBdry (K := K) q γ s) ((![1, 0, 1] : Fin 3 → ℕ) s)) =
      (γ * γ) • pureE_OE q := by
  have hf : (fun s : Fin 3 => (polyBdry (K := K) q γ s) ((![1, 0, 1] : Fin 3 → ℕ) s)) =
      Function.update (Function.update (fun s : Fin 3 => eO (K := K) (q + 1) s)
        (⟨0, by omega⟩ : Fin 3) (γ • E (K := K) q ⟨0, by omega⟩))
        (⟨2, by omega⟩ : Fin 3) (γ • E (K := K) q ⟨2, by omega⟩) := by
    funext s; fin_cases s
    · show (polyBdry q γ ⟨0, by omega⟩) 1 = _
      rw [polyBdry_eval1, Function.update_of_ne (by decide), Function.update_self]
    · show (polyBdry q γ ⟨1, by omega⟩) 0 = _
      rw [polyBdry_eval0, Function.update_of_ne (by decide), Function.update_of_ne (by decide)]
    · show (polyBdry q γ ⟨2, by omega⟩) 1 = _
      rw [polyBdry_eval1, Function.update_self]
  rw [hf]
  rw [tprod_pull_two_smul_general q ⟨0, by omega⟩ ⟨2, by omega⟩ (by decide)]
  show (γ * γ) • tprod K _ = (γ * γ) • pureE_OE q
  congr 1
  show tprod K _ = pureE_OE q
  unfold pureE_OE
  congr 1; funext s; fin_cases s
  · show Function.update (Function.update _ (⟨0, by omega⟩ : Fin 3) _)
      (⟨2, by omega⟩ : Fin 3) _ ⟨0, by omega⟩ = _
    rw [Function.update_of_ne (by decide), Function.update_self]
  · show Function.update (Function.update _ (⟨0, by omega⟩ : Fin 3) _)
      (⟨2, by omega⟩ : Fin 3) _ ⟨1, by omega⟩ = _
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]
  · show Function.update (Function.update _ (⟨0, by omega⟩ : Fin 3) _)
      (⟨2, by omega⟩ : Fin 3) _ ⟨2, by omega⟩ = _
    rw [Function.update_self]

private lemma polyBdry_tprod_eval_011 (q : ℕ) (γ : K) :
    tprod K (fun s : Fin 3 => (polyBdry (K := K) q γ s) ((![0, 1, 1] : Fin 3 → ℕ) s)) =
      (γ * γ) • pureO_EE q := by
  have hf : (fun s : Fin 3 => (polyBdry (K := K) q γ s) ((![0, 1, 1] : Fin 3 → ℕ) s)) =
      Function.update (Function.update (fun s : Fin 3 => eO (K := K) (q + 1) s)
        (⟨1, by omega⟩ : Fin 3) (γ • E (K := K) q ⟨1, by omega⟩))
        (⟨2, by omega⟩ : Fin 3) (γ • E (K := K) q ⟨2, by omega⟩) := by
    funext s; fin_cases s
    · show (polyBdry q γ ⟨0, by omega⟩) 0 = _
      rw [polyBdry_eval0, Function.update_of_ne (by decide), Function.update_of_ne (by decide)]
    · show (polyBdry q γ ⟨1, by omega⟩) 1 = _
      rw [polyBdry_eval1, Function.update_of_ne (by decide), Function.update_self]
    · show (polyBdry q γ ⟨2, by omega⟩) 1 = _
      rw [polyBdry_eval1, Function.update_self]
  rw [hf]
  rw [tprod_pull_two_smul_general q ⟨1, by omega⟩ ⟨2, by omega⟩ (by decide)]
  show (γ * γ) • tprod K _ = (γ * γ) • pureO_EE q
  congr 1
  show tprod K _ = pureO_EE q
  unfold pureO_EE
  congr 1; funext s; fin_cases s
  · show Function.update (Function.update _ (⟨1, by omega⟩ : Fin 3) _)
      (⟨2, by omega⟩ : Fin 3) _ ⟨0, by omega⟩ = _
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]
  · show Function.update (Function.update _ (⟨1, by omega⟩ : Fin 3) _)
      (⟨2, by omega⟩ : Fin 3) _ ⟨1, by omega⟩ = _
    rw [Function.update_of_ne (by decide), Function.update_self]
  · show Function.update (Function.update _ (⟨1, by omega⟩ : Fin 3) _)
      (⟨2, by omega⟩ : Fin 3) _ ⟨2, by omega⟩ = _
    rw [Function.update_self]

/-! ### polyMid at cross tuples — direct CWMonom output -/

private lemma polyMid_tprod_eval_110 (q : ℕ) (i : Fin (q + 1)) :
    tprod K (fun s : Fin 3 => (polyMid (K := K) q i s) ((![1, 1, 0] : Fin 3 → ℕ) s)) =
      CWMonom K (q + 1) (M (q + 1) i) (M (q + 1) i) (O (q + 1)) := by
  unfold CWMonom
  congr 1; funext s; fin_cases s
  · show (polyMid q i ⟨0, by omega⟩) 1 = _
    rw [polyMid_eval1]; rfl
  · show (polyMid q i ⟨1, by omega⟩) 1 = _
    rw [polyMid_eval1]; rfl
  · show (polyMid q i ⟨2, by omega⟩) 0 = _
    rw [polyMid_eval0]; rfl

private lemma polyMid_tprod_eval_101 (q : ℕ) (i : Fin (q + 1)) :
    tprod K (fun s : Fin 3 => (polyMid (K := K) q i s) ((![1, 0, 1] : Fin 3 → ℕ) s)) =
      CWMonom K (q + 1) (M (q + 1) i) (O (q + 1)) (M (q + 1) i) := by
  unfold CWMonom
  congr 1; funext s; fin_cases s
  · show (polyMid q i ⟨0, by omega⟩) 1 = _
    rw [polyMid_eval1]; rfl
  · show (polyMid q i ⟨1, by omega⟩) 0 = _
    rw [polyMid_eval0]; rfl
  · show (polyMid q i ⟨2, by omega⟩) 1 = _
    rw [polyMid_eval1]; rfl

private lemma polyMid_tprod_eval_011 (q : ℕ) (i : Fin (q + 1)) :
    tprod K (fun s : Fin 3 => (polyMid (K := K) q i s) ((![0, 1, 1] : Fin 3 → ℕ) s)) =
      CWMonom K (q + 1) (O (q + 1)) (M (q + 1) i) (M (q + 1) i) := by
  unfold CWMonom
  congr 1; funext s; fin_cases s
  · show (polyMid q i ⟨0, by omega⟩) 0 = _
    rw [polyMid_eval0]; rfl
  · show (polyMid q i ⟨1, by omega⟩) 1 = _
    rw [polyMid_eval1]; rfl
  · show (polyMid q i ⟨2, by omega⟩) 1 = _
    rw [polyMid_eval1]; rfl

/-! ### Order-2 coefficient -/

/-- The order-2 coefficient identity: `Phi.coeff 2 = CWTensor K (q+1)`,
assuming `(q+2:K) ≠ 0` and `(q+2)·γ² = (1+γ)²`. -/
private lemma Phi_coeff_two (q : ℕ) (γ : K) (hQ : (q + 2 : K) ≠ 0)
    (hγ : (q + 2 : K) * γ * γ = (1 + γ) * (1 + γ)) :
    (Phi (K := K) q γ).coeff 2 = CWTensor K (q + 1) := by
  rw [Phi_coeff_split]
  rw [sum_over_antidiag_two (fun m => tprod K (fun i => (polyComp (K := K) q γ i) (m i)))]
  rw [sum_over_antidiag_two (fun m => tprod K (fun i => (polyBdry (K := K) q γ i) (m i)))]
  rw [show (∑ i : Fin (q + 1), (Finset.Nat.antidiagonalTuple 3 2).sum
        (fun m => tprod K (fun s => (polyMid (K := K) q i s) (m s)))) =
      ∑ i : Fin (q + 1),
        (tprod K (fun s => (polyMid (K := K) q i s) ((![2, 0, 0] : Fin 3 → ℕ) s)) +
         tprod K (fun s => (polyMid (K := K) q i s) ((![0, 2, 0] : Fin 3 → ℕ) s)) +
         tprod K (fun s => (polyMid (K := K) q i s) ((![0, 0, 2] : Fin 3 → ℕ) s)) +
         tprod K (fun s => (polyMid (K := K) q i s) ((![1, 1, 0] : Fin 3 → ℕ) s)) +
         tprod K (fun s => (polyMid (K := K) q i s) ((![1, 0, 1] : Fin 3 → ℕ) s)) +
         tprod K (fun s => (polyMid (K := K) q i s) ((![0, 1, 1] : Fin 3 → ℕ) s))) from by
    apply Finset.sum_congr rfl
    intro i _
    exact sum_over_antidiag_two _]
  rw [polyComp_tprod_eval_200, polyComp_tprod_eval_020, polyComp_tprod_eval_002,
      polyComp_tprod_eval_110 q γ hQ, polyComp_tprod_eval_101 q γ hQ,
      polyComp_tprod_eval_011 q γ hQ,
      polyBdry_tprod_eval_200, polyBdry_tprod_eval_020, polyBdry_tprod_eval_002,
      polyBdry_tprod_eval_110, polyBdry_tprod_eval_101, polyBdry_tprod_eval_011]
  -- Distribute the mid sum
  rw [show (∑ i : Fin (q + 1),
      (tprod K (fun s => (polyMid (K := K) q i s) ((![2, 0, 0] : Fin 3 → ℕ) s)) +
       tprod K (fun s => (polyMid (K := K) q i s) ((![0, 2, 0] : Fin 3 → ℕ) s)) +
       tprod K (fun s => (polyMid (K := K) q i s) ((![0, 0, 2] : Fin 3 → ℕ) s)) +
       tprod K (fun s => (polyMid (K := K) q i s) ((![1, 1, 0] : Fin 3 → ℕ) s)) +
       tprod K (fun s => (polyMid (K := K) q i s) ((![1, 0, 1] : Fin 3 → ℕ) s)) +
       tprod K (fun s => (polyMid (K := K) q i s) ((![0, 1, 1] : Fin 3 → ℕ) s)))) =
    (∑ i : Fin (q + 1),
       tprod K (fun s => (polyMid (K := K) q i s) ((![2, 0, 0] : Fin 3 → ℕ) s))) +
    (∑ i : Fin (q + 1),
       tprod K (fun s => (polyMid (K := K) q i s) ((![0, 2, 0] : Fin 3 → ℕ) s))) +
    (∑ i : Fin (q + 1),
       tprod K (fun s => (polyMid (K := K) q i s) ((![0, 0, 2] : Fin 3 → ℕ) s))) +
    (∑ i : Fin (q + 1),
       tprod K (fun s => (polyMid (K := K) q i s) ((![1, 1, 0] : Fin 3 → ℕ) s))) +
    (∑ i : Fin (q + 1),
       tprod K (fun s => (polyMid (K := K) q i s) ((![1, 0, 1] : Fin 3 → ℕ) s))) +
    (∑ i : Fin (q + 1),
       tprod K (fun s => (polyMid (K := K) q i s) ((![0, 1, 1] : Fin 3 → ℕ) s))) from by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
        ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]]
  -- Mid at boundary tuples is 0
  rw [show (∑ i : Fin (q + 1),
      tprod K (fun s => (polyMid (K := K) q i s) ((![2, 0, 0] : Fin 3 → ℕ) s))) = 0 from by
    apply Finset.sum_eq_zero; intro i _; exact polyMid_tprod_eval_200 q i]
  rw [show (∑ i : Fin (q + 1),
      tprod K (fun s => (polyMid (K := K) q i s) ((![0, 2, 0] : Fin 3 → ℕ) s))) = 0 from by
    apply Finset.sum_eq_zero; intro i _; exact polyMid_tprod_eval_020 q i]
  rw [show (∑ i : Fin (q + 1),
      tprod K (fun s => (polyMid (K := K) q i s) ((![0, 0, 2] : Fin 3 → ℕ) s))) = 0 from by
    apply Finset.sum_eq_zero; intro i _; exact polyMid_tprod_eval_002 q i]
  -- Mid at cross tuples gives CWMonom sums
  rw [show (∑ i : Fin (q + 1),
      tprod K (fun s => (polyMid (K := K) q i s) ((![1, 1, 0] : Fin 3 → ℕ) s))) =
      ∑ i : Fin (q + 1), CWMonom K (q + 1) (M (q + 1) i) (M (q + 1) i) (O (q + 1)) from by
    apply Finset.sum_congr rfl; intro i _; exact polyMid_tprod_eval_110 q i]
  rw [show (∑ i : Fin (q + 1),
      tprod K (fun s => (polyMid (K := K) q i s) ((![1, 0, 1] : Fin 3 → ℕ) s))) =
      ∑ i : Fin (q + 1), CWMonom K (q + 1) (M (q + 1) i) (O (q + 1)) (M (q + 1) i) from by
    apply Finset.sum_congr rfl; intro i _; exact polyMid_tprod_eval_101 q i]
  rw [show (∑ i : Fin (q + 1),
      tprod K (fun s => (polyMid (K := K) q i s) ((![0, 1, 1] : Fin 3 → ℕ) s))) =
      ∑ i : Fin (q + 1), CWMonom K (q + 1) (O (q + 1)) (M (q + 1) i) (M (q + 1) i) from by
    apply Finset.sum_congr rfl; intro i _; exact polyMid_tprod_eval_011 q i]
  -- Now we have:
  -- Comp: (0+0+0) + c•pureEE_O + c•pureE_OE + c•pureO_EE  where c = -(1+γ)·(1+γ)/(q+2)
  -- Mid:  (0+0+0) + (∑M_iM_iO) + (∑M_iOM_i) + (∑OM_iM_i)
  -- Bdry: (TOO + OTO + OOT) + (γ²)•pureEE_O + (γ²)•pureE_OE + (γ²)•pureO_EE
  -- Goal: sum these = CWTensor K (q+1)
  -- The pure cancellations: -(1+γ)(1+γ)/(q+2) + γ² = 0 (using (q+2)γ² = (1+γ)²)
  -- Let c := -(1+γ)*(1+γ)/(q+2), so c + γ² = 0.
  have hcancel : (-(1 + γ) * ((1 + γ) / (q + 2 : K))) + γ * γ = 0 := by
    have h1 : (1 + γ) * (1 + γ) = (q + 2 : K) * γ * γ := hγ.symm
    rw [show (-(1 + γ) * ((1 + γ) / (q + 2 : K))) = -((1 + γ) * (1 + γ)) / (q + 2 : K) from by
      field_simp]
    rw [h1]
    field_simp
    ring
  -- Combine boundary tuple Bdry only contributions: TOO + OTO + OOT (boundary monomials)
  -- Plus pure cross-tuple cancellation: c•P + γ²•P = (c+γ²)•P = 0 for each P (pureEE_O etc.)
  -- Plus mid CWMonom sums = (∑i M_iM_iO + M_iOM_i + OM_iM_i) (CW interior monomials)
  -- Combine to get CWTensor K (q+1)
  set TOO := CWMonom K (q + 1) (T (q + 1)) (O (q + 1)) (O (q + 1)) with hTOO
  set OTO := CWMonom K (q + 1) (O (q + 1)) (T (q + 1)) (O (q + 1)) with hOTO
  set OOT := CWMonom K (q + 1) (O (q + 1)) (O (q + 1)) (T (q + 1)) with hOOT
  set MMO := fun i : Fin (q + 1) => CWMonom K (q + 1) (M (q + 1) i) (M (q + 1) i) (O (q + 1))
    with hMMO
  set MOM := fun i : Fin (q + 1) => CWMonom K (q + 1) (M (q + 1) i) (O (q + 1)) (M (q + 1) i)
    with hMOM
  set OMM := fun i : Fin (q + 1) => CWMonom K (q + 1) (O (q + 1)) (M (q + 1) i) (M (q + 1) i)
    with hOMM
  set P0 := pureEE_O (K := K) q with hP0
  set P1 := pureE_OE (K := K) q with hP1
  set P2 := pureO_EE (K := K) q with hP2
  set c : K := -(1 + γ) * ((1 + γ) / (q + 2 : K)) with hc
  -- The goal at this point is the unsimplified sum.
  -- LHS = (0 + 0 + 0 + c•P0 + c•P1 + c•P2) + (0 + 0 + 0 + ∑MMO + ∑MOM + ∑OMM) +
  --       (TOO + OTO + OOT + (γ*γ)•P0 + (γ*γ)•P1 + (γ*γ)•P2)
  -- Need: LHS = CWTensor K (q+1) = ∑i (OMM_i + MOM_i + MMO_i) + OOT + OTO + TOO
  have hpureEE_O_zero : c • P0 + (γ * γ) • P0 = 0 := by
    rw [← add_smul, hcancel, zero_smul]
  have hpureE_OE_zero : c • P1 + (γ * γ) • P1 = 0 := by
    rw [← add_smul, hcancel, zero_smul]
  have hpureO_EE_zero : c • P2 + (γ * γ) • P2 = 0 := by
    rw [← add_smul, hcancel, zero_smul]
  -- Now compute CWTensor K (q+1). By definition.
  have hCWT : CWTensor K (q + 1) =
      (∑ i : Fin (q + 1), (OMM i + MOM i + MMO i)) + OOT + OTO + TOO := rfl
  rw [hCWT]
  -- Reorganize LHS. We want it to come out to (∑i (OMM i + MOM i + MMO i)) + OOT + OTO + TOO.
  -- LHS currently:
  -- (0 + 0 + 0 + c•P0 + c•P1 + c•P2)
  --  + (0 + 0 + 0 + ∑MMO + ∑MOM + ∑OMM)
  --  + (TOO + OTO + OOT + γ*γ•P0 + γ*γ•P1 + γ*γ•P2)
  -- Goal after rw:
  -- (∑i OMM_i + MOM_i + MMO_i) + OOT + OTO + TOO
  -- Rearrange using `abel` after using pure cancellations.
  have hgoal :
    ((0 + 0 + 0 + c • P0 + c • P1 + c • P2) +
     (0 + 0 + 0 + (∑ i, MMO i) + (∑ i, MOM i) + (∑ i, OMM i)) +
     (TOO + OTO + OOT + (γ * γ) • P0 + (γ * γ) • P1 + (γ * γ) • P2))
    = (∑ i, (OMM i + MOM i + MMO i)) + OOT + OTO + TOO := by
    have hPexp : c • P0 + c • P1 + c • P2 + ((γ * γ) • P0 + (γ * γ) • P1 + (γ * γ) • P2) =
        (c • P0 + (γ * γ) • P0) + (c • P1 + (γ * γ) • P1) + (c • P2 + (γ * γ) • P2) := by abel
    have hsum_split : (∑ i, (OMM i + MOM i + MMO i)) =
        (∑ i, OMM i) + (∑ i, MOM i) + (∑ i, MMO i) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    rw [hsum_split]
    calc (0 + 0 + 0 + c • P0 + c • P1 + c • P2) +
           (0 + 0 + 0 + (∑ i, MMO i) + (∑ i, MOM i) + (∑ i, OMM i)) +
           (TOO + OTO + OOT + (γ * γ) • P0 + (γ * γ) • P1 + (γ * γ) • P2)
        = ((c • P0 + (γ * γ) • P0) + (c • P1 + (γ * γ) • P1) + (c • P2 + (γ * γ) • P2))
            + ((∑ i, OMM i) + (∑ i, MOM i) + (∑ i, MMO i)) + (OOT + OTO + TOO) := by abel
      _ = (0 + 0 + 0)
            + ((∑ i, OMM i) + (∑ i, MOM i) + (∑ i, MMO i)) + (OOT + OTO + TOO) := by
            rw [hpureEE_O_zero, hpureE_OE_zero, hpureO_EE_zero]
      _ = (∑ i, OMM i) + (∑ i, MOM i) + (∑ i, MMO i) + OOT + OTO + TOO := by abel
  -- Substitute back the definitions
  exact hgoal

end MME.CWPhiCoeffTwoSol

/-! ## Final assembly: the `solution` theorem -/

open MME

/-- Top-level solution: the order-2 CW degeneration witness under the
algebraic identity `(q+2)·γ² = (1+γ)²`. -/
theorem solution {K : Type u} [Field K] (q : ℕ) (γ : K)
    (hQ : (q + 2 : K) ≠ 0)
    (hγ : (q + 2 : K) * γ * γ = (1 + γ) * (1 + γ)) :
    DegeneratesOfOrder (CWObj K (q + 1)) (TensorObj.diagObj K 3 ((q + 1) + 2)) 2 := by
  refine ⟨MME.CWPhiCoeffTwoSol.Phi (K := K) q γ, ?_, ?_⟩
  · intro k hk
    match k, hk with
    | 0, _ => exact MME.CWPhiCoeffTwoSol.Phi_coeff_zero q γ
    | 1, _ => exact MME.CWPhiCoeffTwoSol.Phi_coeff_one q γ hQ
  · exact MME.CWPhiCoeffTwoSol.Phi_coeff_two q γ hQ hγ

