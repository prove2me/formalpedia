-- Prove2me | solution 1 for mme_CW_border_rank_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-23T22:43:52.408883+00:00
-- url     : https://prove2.me/submissions/da68062c-029a-43ee-8fde-c7d57392de07

import Mathlib.Data.Fin.VecNotation
import Definitions.Def_mme_CW_tensor
import Definitions.Def_mme_degeneration

/-!
# The characteristic-free Coppersmith--Winograd order-three degeneration

This formalizes the numerator of CW90, equation (10):

`Σᵢ ε (e₀ + εeᵢ)³ - (e₀ + ε² Σᵢeᵢ)³
  + (1 - qε) (e₀ + ε³e_{q+1})³`.

The coefficients below degree three cancel and the coefficient of degree three
is exactly `CWTensor K q`.  Unlike the tempting symmetric order-two ansatz, this
identity is valid over every field.
-/

open MME PiTensorProduct BigOperators Finset

universe u

set_option maxHeartbeats 4000000
set_option maxRecDepth 4000

namespace MME.CWBorderRank

variable {K : Type u} [Field K] (q : ℕ)

private noncomputable def O : Fin (q + 2) := ⟨0, by omega⟩
private noncomputable def T : Fin (q + 2) := ⟨q + 1, by omega⟩
private noncomputable def M (i : Fin q) : Fin (q + 2) := ⟨i.val + 1, by omega⟩

private noncomputable def e (a : Fin (q + 2)) (s : Fin 3) : CWSpace K q s :=
  match s with
  | ⟨0, _⟩ => Pi.single a 1
  | ⟨1, _⟩ => Pi.single a 1
  | ⟨2, _⟩ => Pi.single a 1

private noncomputable def S (s : Fin 3) : CWSpace K q s :=
  ∑ i : Fin q, e q (M q i) s

/-! The `q` main slots encode `ε(e₀+εeᵢ)^{⊗3}`. -/
private noncomputable def mainVec (i : Fin q) (s : Fin 3) :
    ℕ →₀ CWSpace K q s :=
  match s with
  | ⟨0, _⟩ => Finsupp.single 1 (e q (O q) 0) + Finsupp.single 2 (e q (M q i) 0)
  | ⟨1, _⟩ => Finsupp.single 0 (e q (O q) 1) + Finsupp.single 1 (e q (M q i) 1)
  | ⟨2, _⟩ => Finsupp.single 0 (e q (O q) 2) + Finsupp.single 1 (e q (M q i) 2)

/-! The first correction slot encodes `-(e₀+ε²Σᵢeᵢ)^{⊗3}`. -/
private noncomputable def sumVec (s : Fin 3) : ℕ →₀ CWSpace K q s :=
  match s with
  | ⟨0, _⟩ => Finsupp.single 0 (-(e q (O q) 0)) + Finsupp.single 2 (-(S q 0))
  | ⟨1, _⟩ => Finsupp.single 0 (e q (O q) 1) + Finsupp.single 2 (S q 1)
  | ⟨2, _⟩ => Finsupp.single 0 (e q (O q) 2) + Finsupp.single 2 (S q 2)

/-! The last slot encodes `(1-qε)(e₀+ε³e_{q+1})^{⊗3}`. -/
private noncomputable def topVec (s : Fin 3) : ℕ →₀ CWSpace K q s :=
  match s with
  | ⟨0, _⟩ =>
      Finsupp.single 0 (e q (O q) 0) +
      Finsupp.single 1 ((-(q : K)) • e q (O q) 0) +
      Finsupp.single 3 (e q (T q) 0) +
      Finsupp.single 4 ((-(q : K)) • e q (T q) 0)
  | ⟨1, _⟩ => Finsupp.single 0 (e q (O q) 1) + Finsupp.single 3 (e q (T q) 1)
  | ⟨2, _⟩ => Finsupp.single 0 (e q (O q) 2) + Finsupp.single 3 (e q (T q) 2)

private noncomputable def idxEquiv : Fin q ⊕ Fin 2 ≃ Fin (q + 2) := finSumFinEquiv

private noncomputable def vfun : Fin (q + 2) → ∀ s : Fin 3, ℕ →₀ CWSpace K q s :=
  fun j =>
    match (idxEquiv q).symm j with
    | Sum.inl i => mainVec q i
    | Sum.inr r => if r = 0 then sumVec q else topVec q

private lemma vfun_main (i : Fin q) :
    vfun (K := K) q (idxEquiv q (Sum.inl i)) = mainVec q i := by
  simp only [vfun, Equiv.symm_apply_apply]

private lemma vfun_sum :
    vfun (K := K) q (idxEquiv q (Sum.inr (0 : Fin 2))) = sumVec q := by
  simp only [vfun, Equiv.symm_apply_apply, ↓reduceIte]

private lemma vfun_top :
    vfun (K := K) q (idxEquiv q (Sum.inr (1 : Fin 2))) = topVec q := by
  simp only [vfun, Equiv.symm_apply_apply]
  simp

private noncomputable def vlin (s : Fin 3) (k : ℕ) :
    (TensorObj.diagObj K 3 (q + 2)).V s →ₗ[K] (CWObj K q).V s :=
  (Pi.basisFun K (Fin (q + 2))).constr K (fun j => vfun q j s k)

private lemma vlin_support (s : Fin 3) :
    ∀ k : ℕ, vlin (K := K) q s k ≠ 0 →
      k ∈ Finset.univ.biUnion (fun j : Fin (q + 2) => (vfun (K := K) q j s).support) := by
  intro k hne
  rw [Finset.mem_biUnion]
  by_contra hall
  push Not at hall
  apply hne
  have hz : (fun j : Fin (q + 2) => (vfun (K := K) q j s) k) =
      (0 : Fin (q + 2) → (CWObj K q).V s) :=
    funext fun j => Finsupp.notMem_support_iff.mp (hall j (Finset.mem_univ j))
  show (Pi.basisFun K (Fin (q + 2))).constr K
      (fun j => (vfun (K := K) q j s) k) = 0
  rw [hz]
  exact map_zero _

private noncomputable def Phi :
    PolyFamily (CWObj K q) (TensorObj.diagObj K 3 (q + 2)) where
  A := fun s => Finsupp.onFinset _ _ (vlin_support q s)

private lemma Phi_A_apply (s : Fin 3) (k : ℕ) :
    (Phi (K := K) q).A s k = vlin q s k := rfl

private lemma vlin_single (s : Fin 3) (k : ℕ) (j : Fin (q + 2)) :
    vlin (K := K) q s k (Pi.single j 1) = (vfun q j s) k := by
  show (Pi.basisFun K (Fin (q + 2))).constr K
      (fun j' => (vfun (K := K) q j' s) k)
      (Pi.single j 1) = _
  rw [show (Pi.single j (1 : K) : Fin (q + 2) → K) =
      (Pi.basisFun K (Fin (q + 2))) j from
        (Pi.basisFun_apply K (Fin (q + 2)) j).symm]
  exact Module.Basis.constr_basis (Pi.basisFun K (Fin (q + 2))) K _ j

private noncomputable def termCoeff
    (v : ∀ s : Fin 3, ℕ →₀ CWSpace K q s) (k : ℕ) :
    PiTensorProduct K (CWSpace K q) :=
  (Finset.Nat.antidiagonalTuple 3 k).sum
    (fun m => tprod K (fun s => v s (m s)))

private noncomputable def tensorAt
    (v : ∀ s : Fin 3, ℕ →₀ CWSpace K q s) (a b c : ℕ) :
    PiTensorProduct K (CWSpace K q) :=
  tprod K (fun s => v s (![a, b, c] s))

private lemma Phi_coeff_expand (k : ℕ) :
    (Phi (K := K) q).coeff k =
      ∑ j : Fin (q + 2), termCoeff (K := K) q (vfun q j) k := by
  unfold PolyFamily.coeff termCoeff
  have hY : (TensorObj.diagObj K 3 (q + 2)).t =
      ∑ j : Fin (q + 2),
        tprod K (fun (_ : Fin 3) => (Pi.single j 1 : Fin (q + 2) → K)) := rfl
  simp_rw [hY]
  rw [Finset.sum_congr rfl (fun m _ =>
    map_sum (PiTensorProduct.map (fun s => (Phi (K := K) q).A s (m s)))
      (fun j : Fin (q + 2) => tprod K fun _ =>
        (Pi.single j 1 : Fin (q + 2) → K)) Finset.univ),
    Finset.sum_comm]
  congr 1
  ext j
  congr 1
  ext m
  have hmap := PiTensorProduct.map_tprod
    (R := K) (f := fun s => (Phi (K := K) q).A s (m s))
    (x := fun _ : Fin 3 => (Pi.single j 1 : Fin (q + 2) → K))
  refine hmap.trans ?_
  congr 1
  funext s
  rw [Phi_A_apply]
  exact vlin_single q s (m s) j

private lemma Phi_coeff_split (k : ℕ) :
    (Phi (K := K) q).coeff k =
      (∑ i : Fin q, termCoeff (K := K) q (mainVec q i) k) +
      termCoeff (K := K) q (sumVec q) k +
      termCoeff (K := K) q (topVec q) k := by
  rw [Phi_coeff_expand]
  rw [← Equiv.sum_comp (idxEquiv q) (fun j => termCoeff q (vfun q j) k)]
  rw [Fintype.sum_sum_type, Fin.sum_univ_two]
  simp only [vfun_main, vfun_sum, vfun_top]
  abel

private lemma anti_zero :
    Finset.Nat.antidiagonalTuple 3 0 = {![0, 0, 0]} := by decide

private lemma anti_one :
    Finset.Nat.antidiagonalTuple 3 1 =
      {![1, 0, 0], ![0, 1, 0], ![0, 0, 1]} := by decide

private lemma anti_two :
    Finset.Nat.antidiagonalTuple 3 2 =
      {![2, 0, 0], ![1, 1, 0], ![1, 0, 1],
       ![0, 2, 0], ![0, 1, 1], ![0, 0, 2]} := by decide

private lemma anti_three :
    Finset.Nat.antidiagonalTuple 3 3 =
      {![3, 0, 0], ![2, 1, 0], ![2, 0, 1], ![1, 2, 0], ![1, 1, 1],
       ![1, 0, 2], ![0, 3, 0], ![0, 2, 1], ![0, 1, 2], ![0, 0, 3]} := by
  decide

/-! Per-slot coefficient calculations. -/

private lemma main_at_100 (i : Fin q) :
    tensorAt (K := K) q (mainVec q i) 1 0 0 =
      CWMonom K q (O q) (O q) (O q) := by
  unfold tensorAt CWMonom
  congr 1
  funext s
  fin_cases s <;> simp [mainVec, e]

private lemma main_at_200 (i : Fin q) :
    tensorAt (K := K) q (mainVec q i) 2 0 0 =
      CWMonom K q (M q i) (O q) (O q) := by
  unfold tensorAt CWMonom
  congr 1
  funext s
  fin_cases s <;> simp [mainVec, e]

private lemma main_at_110 (i : Fin q) :
    tensorAt (K := K) q (mainVec q i) 1 1 0 =
      CWMonom K q (O q) (M q i) (O q) := by
  unfold tensorAt CWMonom
  congr 1
  funext s
  fin_cases s <;> simp [mainVec, e]

private lemma main_at_101 (i : Fin q) :
    tensorAt (K := K) q (mainVec q i) 1 0 1 =
      CWMonom K q (O q) (O q) (M q i) := by
  unfold tensorAt CWMonom
  congr 1
  funext s
  fin_cases s <;> simp [mainVec, e]

private lemma main_at_210 (i : Fin q) :
    tensorAt (K := K) q (mainVec q i) 2 1 0 =
      CWMonom K q (M q i) (M q i) (O q) := by
  unfold tensorAt CWMonom
  congr 1
  funext s
  fin_cases s <;> simp [mainVec, e]

private lemma main_at_201 (i : Fin q) :
    tensorAt (K := K) q (mainVec q i) 2 0 1 =
      CWMonom K q (M q i) (O q) (M q i) := by
  unfold tensorAt CWMonom
  congr 1
  funext s
  fin_cases s <;> simp [mainVec, e]

private lemma main_at_111 (i : Fin q) :
    tensorAt (K := K) q (mainVec q i) 1 1 1 =
      CWMonom K q (O q) (M q i) (M q i) := by
  unfold tensorAt CWMonom
  congr 1
  funext s
  fin_cases s <;> simp [mainVec, e]

private lemma main_at_zero_of_mode0_zero (i : Fin q) (b c : ℕ) :
    tensorAt (K := K) q (mainVec q i) 0 b c = 0 := by
  unfold tensorAt
  apply (PiTensorProduct.tprod K).map_coord_zero (0 : Fin 3)
  simp [mainVec]

private lemma main_at_zero_of_mode0_ge3 (i : Fin q) (a b c : ℕ) (ha : 3 ≤ a) :
    tensorAt (K := K) q (mainVec q i) a b c = 0 := by
  unfold tensorAt
  apply (PiTensorProduct.tprod K).map_coord_zero (0 : Fin 3)
  simp [mainVec, Finsupp.single_apply, if_neg (by omega : (1 : ℕ) ≠ a),
    if_neg (by omega : (2 : ℕ) ≠ a)]

private lemma main_at_zero_of_mode1_ge2 (i : Fin q) (a b c : ℕ) (hb : 2 ≤ b) :
    tensorAt (K := K) q (mainVec q i) a b c = 0 := by
  unfold tensorAt
  apply (PiTensorProduct.tprod K).map_coord_zero (1 : Fin 3)
  simp [mainVec, Finsupp.single_apply, if_neg (by omega : (0 : ℕ) ≠ b),
    if_neg (by omega : (1 : ℕ) ≠ b)]

private lemma main_at_zero_of_mode2_ge2 (i : Fin q) (a b c : ℕ) (hc : 2 ≤ c) :
    tensorAt (K := K) q (mainVec q i) a b c = 0 := by
  unfold tensorAt
  apply (PiTensorProduct.tprod K).map_coord_zero (2 : Fin 3)
  simp [mainVec, Finsupp.single_apply, if_neg (by omega : (0 : ℕ) ≠ c),
    if_neg (by omega : (1 : ℕ) ≠ c)]

private lemma tprod_S_mode0 :
    tprod K (Function.update (fun s : Fin 3 => e q (O q) s) (0 : Fin 3) (S q 0)) =
      ∑ i : Fin q, CWMonom K q (M q i) (O q) (O q) := by
  rw [S, (PiTensorProduct.tprod K).map_update_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  unfold CWMonom
  congr 1
  funext s
  fin_cases s <;> simp [e]

private lemma tprod_S_mode1 :
    tprod K (Function.update (fun s : Fin 3 => e q (O q) s) (1 : Fin 3) (S q 1)) =
      ∑ i : Fin q, CWMonom K q (O q) (M q i) (O q) := by
  rw [S, (PiTensorProduct.tprod K).map_update_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  unfold CWMonom
  congr 1
  funext s
  fin_cases s <;> simp [e]

private lemma tprod_S_mode2 :
    tprod K (Function.update (fun s : Fin 3 => e q (O q) s) (2 : Fin 3) (S q 2)) =
      ∑ i : Fin q, CWMonom K q (O q) (O q) (M q i) := by
  rw [S, (PiTensorProduct.tprod K).map_update_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  unfold CWMonom
  congr 1
  funext s
  fin_cases s <;> simp [e]

private lemma sum_at_000 :
    tensorAt (K := K) q (sumVec q) 0 0 0 =
      -(CWMonom K q (O q) (O q) (O q)) := by
  unfold tensorAt
  have hfun : (fun s : Fin 3 => (sumVec (K := K) q s) (![0, 0, 0] s)) =
      Function.update (fun s : Fin 3 => e q (O q) s) (0 : Fin 3) (-(e q (O q) 0)) := by
    funext s
    fin_cases s <;> simp [sumVec, e]
  rw [hfun, (PiTensorProduct.tprod K).map_update_neg, Function.update_eq_self]
  rfl

private lemma sum_at_200 :
    tensorAt (K := K) q (sumVec q) 2 0 0 =
      -(∑ i : Fin q, CWMonom K q (M q i) (O q) (O q)) := by
  unfold tensorAt
  have hfun : (fun s : Fin 3 => (sumVec (K := K) q s) (![2, 0, 0] s)) =
      Function.update (fun s : Fin 3 => e q (O q) s) (0 : Fin 3) (-(S q 0)) := by
    funext s
    fin_cases s <;> simp [sumVec]
  rw [hfun, (PiTensorProduct.tprod K).map_update_neg, tprod_S_mode0]

private lemma sum_at_020 :
    tensorAt (K := K) q (sumVec q) 0 2 0 =
      -(∑ i : Fin q, CWMonom K q (O q) (M q i) (O q)) := by
  unfold tensorAt
  have hfun : (fun s : Fin 3 => (sumVec (K := K) q s) (![0, 2, 0] s)) =
      Function.update
        (Function.update (fun s : Fin 3 => e q (O q) s) (1 : Fin 3) (S q 1))
        (0 : Fin 3) (-(e q (O q) 0)) := by
    funext s
    fin_cases s <;> simp [sumVec, e]
  rw [hfun, (PiTensorProduct.tprod K).map_update_neg]
  have hupd :
      Function.update
          (Function.update (fun s : Fin 3 => e (K := K) q (O q) s) (1 : Fin 3)
            (S (K := K) q 1))
          (0 : Fin 3) (e (K := K) q (O q) 0) =
        Function.update (fun s : Fin 3 => e (K := K) q (O q) s) (1 : Fin 3)
          (S (K := K) q 1) := by
    funext s
    fin_cases s <;> simp [e]
  rw [hupd, tprod_S_mode1 (K := K) q]

private lemma sum_at_002 :
    tensorAt (K := K) q (sumVec q) 0 0 2 =
      -(∑ i : Fin q, CWMonom K q (O q) (O q) (M q i)) := by
  unfold tensorAt
  have hfun : (fun s : Fin 3 => (sumVec (K := K) q s) (![0, 0, 2] s)) =
      Function.update
        (Function.update (fun s : Fin 3 => e q (O q) s) (2 : Fin 3) (S q 2))
        (0 : Fin 3) (-(e q (O q) 0)) := by
    funext s
    fin_cases s <;> simp [sumVec, e]
  rw [hfun, (PiTensorProduct.tprod K).map_update_neg]
  have hupd :
      Function.update
          (Function.update (fun s : Fin 3 => e (K := K) q (O q) s) (2 : Fin 3)
            (S (K := K) q 2))
          (0 : Fin 3) (e (K := K) q (O q) 0) =
        Function.update (fun s : Fin 3 => e (K := K) q (O q) s) (2 : Fin 3)
          (S (K := K) q 2) := by
    funext s
    fin_cases s <;> simp [e]
  rw [hupd, tprod_S_mode2 (K := K) q]

private lemma sum_at_zero_of_mode0 (a b c : ℕ) (ha0 : a ≠ 0) (ha2 : a ≠ 2) :
    tensorAt (K := K) q (sumVec q) a b c = 0 := by
  unfold tensorAt
  apply (PiTensorProduct.tprod K).map_coord_zero (0 : Fin 3)
  simp [sumVec, Finsupp.single_apply, if_neg (Ne.symm ha0), if_neg (Ne.symm ha2)]

private lemma sum_at_zero_of_mode1 (a b c : ℕ) (hb0 : b ≠ 0) (hb2 : b ≠ 2) :
    tensorAt (K := K) q (sumVec q) a b c = 0 := by
  unfold tensorAt
  apply (PiTensorProduct.tprod K).map_coord_zero (1 : Fin 3)
  simp [sumVec, Finsupp.single_apply, if_neg (Ne.symm hb0), if_neg (Ne.symm hb2)]

private lemma sum_at_zero_of_mode2 (a b c : ℕ) (hc0 : c ≠ 0) (hc2 : c ≠ 2) :
    tensorAt (K := K) q (sumVec q) a b c = 0 := by
  unfold tensorAt
  apply (PiTensorProduct.tprod K).map_coord_zero (2 : Fin 3)
  simp [sumVec, Finsupp.single_apply, if_neg (Ne.symm hc0), if_neg (Ne.symm hc2)]

private lemma main_coeff_zero (i : Fin q) :
    termCoeff (K := K) q (mainVec q i) 0 = 0 := by
  rw [termCoeff, anti_zero]
  simp only [Finset.sum_singleton]
  apply (PiTensorProduct.tprod K).map_coord_zero (0 : Fin 3)
  simp [mainVec]

private lemma main_coeff_one (i : Fin q) :
    termCoeff (K := K) q (mainVec q i) 1 = CWMonom K q (O q) (O q) (O q) := by
  rw [termCoeff, anti_one]
  change tensorAt q (mainVec q i) 1 0 0 +
    (tensorAt q (mainVec q i) 0 1 0 + tensorAt q (mainVec q i) 0 0 1) = _
  rw [main_at_100, main_at_zero_of_mode0_zero, main_at_zero_of_mode0_zero]
  simp

private lemma main_coeff_two (i : Fin q) :
    termCoeff (K := K) q (mainVec q i) 2 =
      CWMonom K q (M q i) (O q) (O q) +
      CWMonom K q (O q) (M q i) (O q) +
      CWMonom K q (O q) (O q) (M q i) := by
  rw [termCoeff, anti_two]
  change tensorAt q (mainVec q i) 2 0 0 +
    (tensorAt q (mainVec q i) 1 1 0 +
      (tensorAt q (mainVec q i) 1 0 1 +
        (tensorAt q (mainVec q i) 0 2 0 +
          (tensorAt q (mainVec q i) 0 1 1 + tensorAt q (mainVec q i) 0 0 2)))) = _
  rw [main_at_200, main_at_110, main_at_101,
    main_at_zero_of_mode0_zero, main_at_zero_of_mode0_zero,
    main_at_zero_of_mode0_zero]
  abel

private lemma main_coeff_three (i : Fin q) :
    termCoeff (K := K) q (mainVec q i) 3 =
      CWMonom K q (O q) (M q i) (M q i) +
      CWMonom K q (M q i) (O q) (M q i) +
      CWMonom K q (M q i) (M q i) (O q) := by
  rw [termCoeff, anti_three]
  change tensorAt q (mainVec q i) 3 0 0 +
    (tensorAt q (mainVec q i) 2 1 0 +
      (tensorAt q (mainVec q i) 2 0 1 +
        (tensorAt q (mainVec q i) 1 2 0 +
          (tensorAt q (mainVec q i) 1 1 1 +
            (tensorAt q (mainVec q i) 1 0 2 +
              (tensorAt q (mainVec q i) 0 3 0 +
                (tensorAt q (mainVec q i) 0 2 1 +
                  (tensorAt q (mainVec q i) 0 1 2 +
                    tensorAt q (mainVec q i) 0 0 3)))))))) = _
  rw [main_at_zero_of_mode0_ge3, main_at_210, main_at_201,
    main_at_zero_of_mode1_ge2, main_at_111, main_at_zero_of_mode2_ge2,
    main_at_zero_of_mode0_zero, main_at_zero_of_mode0_zero,
    main_at_zero_of_mode0_zero, main_at_zero_of_mode0_zero]
  · abel
  · omega
  · omega
  · omega

private lemma sum_coeff_zero :
    termCoeff (K := K) q (sumVec q) 0 = -(CWMonom K q (O q) (O q) (O q)) := by
  rw [termCoeff, anti_zero]
  change tensorAt q (sumVec q) 0 0 0 = _
  exact sum_at_000 q

private lemma sum_coeff_one : termCoeff (K := K) q (sumVec q) 1 = 0 := by
  rw [termCoeff, anti_one]
  change tensorAt q (sumVec q) 1 0 0 +
    (tensorAt q (sumVec q) 0 1 0 + tensorAt q (sumVec q) 0 0 1) = 0
  rw [sum_at_zero_of_mode0, sum_at_zero_of_mode1, sum_at_zero_of_mode2]
  all_goals simp

private lemma sum_coeff_two :
    termCoeff (K := K) q (sumVec q) 2 =
      -(∑ i : Fin q,
          (CWMonom K q (M q i) (O q) (O q) +
           CWMonom K q (O q) (M q i) (O q) +
           CWMonom K q (O q) (O q) (M q i))) := by
  rw [termCoeff, anti_two]
  change tensorAt q (sumVec q) 2 0 0 +
    (tensorAt q (sumVec q) 1 1 0 +
      (tensorAt q (sumVec q) 1 0 1 +
        (tensorAt q (sumVec q) 0 2 0 +
          (tensorAt q (sumVec q) 0 1 1 + tensorAt q (sumVec q) 0 0 2)))) = _
  rw [sum_at_200, sum_at_zero_of_mode0, sum_at_zero_of_mode0,
    sum_at_020, sum_at_zero_of_mode1, sum_at_002]
  · simp_rw [Finset.sum_add_distrib]
    abel
  all_goals simp

private lemma sum_coeff_three : termCoeff (K := K) q (sumVec q) 3 = 0 := by
  rw [termCoeff, anti_three]
  change tensorAt q (sumVec q) 3 0 0 +
    (tensorAt q (sumVec q) 2 1 0 +
      (tensorAt q (sumVec q) 2 0 1 +
        (tensorAt q (sumVec q) 1 2 0 +
          (tensorAt q (sumVec q) 1 1 1 +
            (tensorAt q (sumVec q) 1 0 2 +
              (tensorAt q (sumVec q) 0 3 0 +
                (tensorAt q (sumVec q) 0 2 1 +
                  (tensorAt q (sumVec q) 0 1 2 +
                    tensorAt q (sumVec q) 0 0 3)))))))) = 0
  rw [sum_at_zero_of_mode0, sum_at_zero_of_mode1, sum_at_zero_of_mode2,
    sum_at_zero_of_mode0, sum_at_zero_of_mode0, sum_at_zero_of_mode0,
    sum_at_zero_of_mode1, sum_at_zero_of_mode2, sum_at_zero_of_mode1,
    sum_at_zero_of_mode2]
  all_goals simp

private lemma top_at_000 :
    tensorAt (K := K) q (topVec q) 0 0 0 =
      CWMonom K q (O q) (O q) (O q) := by
  unfold tensorAt CWMonom
  congr 1
  funext s
  fin_cases s <;> simp [topVec, e]

private lemma top_at_100 :
    tensorAt (K := K) q (topVec q) 1 0 0 =
      (-(q : K)) • CWMonom K q (O q) (O q) (O q) := by
  unfold tensorAt
  have hfun : (fun s : Fin 3 => (topVec (K := K) q s) (![1, 0, 0] s)) =
      Function.update (fun s : Fin 3 => e q (O q) s) (0 : Fin 3)
        ((-(q : K)) • e q (O q) 0) := by
    funext s
    fin_cases s <;> simp [topVec, e]
  rw [hfun, (PiTensorProduct.tprod K).map_update_smul, Function.update_eq_self]
  rfl

private lemma top_at_300 :
    tensorAt (K := K) q (topVec q) 3 0 0 =
      CWMonom K q (T q) (O q) (O q) := by
  unfold tensorAt CWMonom
  congr 1
  funext s
  fin_cases s <;> simp [topVec, e]

private lemma top_at_030 :
    tensorAt (K := K) q (topVec q) 0 3 0 =
      CWMonom K q (O q) (T q) (O q) := by
  unfold tensorAt CWMonom
  congr 1
  funext s
  fin_cases s <;> simp [topVec, e]

private lemma top_at_003 :
    tensorAt (K := K) q (topVec q) 0 0 3 =
      CWMonom K q (O q) (O q) (T q) := by
  unfold tensorAt CWMonom
  congr 1
  funext s
  fin_cases s <;> simp [topVec, e]

private lemma top_at_zero_of_mode0 (a b c : ℕ)
    (ha0 : a ≠ 0) (ha1 : a ≠ 1) (ha3 : a ≠ 3) (ha4 : a ≠ 4) :
    tensorAt (K := K) q (topVec q) a b c = 0 := by
  unfold tensorAt
  apply (PiTensorProduct.tprod K).map_coord_zero (0 : Fin 3)
  simp [topVec, Finsupp.single_apply, if_neg (Ne.symm ha0), if_neg (Ne.symm ha1),
    if_neg (Ne.symm ha3), if_neg (Ne.symm ha4)]

private lemma top_at_zero_of_mode1 (a b c : ℕ) (hb0 : b ≠ 0) (hb3 : b ≠ 3) :
    tensorAt (K := K) q (topVec q) a b c = 0 := by
  unfold tensorAt
  apply (PiTensorProduct.tprod K).map_coord_zero (1 : Fin 3)
  simp [topVec, Finsupp.single_apply, if_neg (Ne.symm hb0), if_neg (Ne.symm hb3)]

private lemma top_at_zero_of_mode2 (a b c : ℕ) (hc0 : c ≠ 0) (hc3 : c ≠ 3) :
    tensorAt (K := K) q (topVec q) a b c = 0 := by
  unfold tensorAt
  apply (PiTensorProduct.tprod K).map_coord_zero (2 : Fin 3)
  simp [topVec, Finsupp.single_apply, if_neg (Ne.symm hc0), if_neg (Ne.symm hc3)]

private lemma top_coeff_zero :
    termCoeff (K := K) q (topVec q) 0 = CWMonom K q (O q) (O q) (O q) := by
  rw [termCoeff, anti_zero]
  change tensorAt q (topVec q) 0 0 0 = _
  exact top_at_000 q

private lemma top_coeff_one :
    termCoeff (K := K) q (topVec q) 1 =
      (-(q : K)) • CWMonom K q (O q) (O q) (O q) := by
  rw [termCoeff, anti_one]
  change tensorAt q (topVec q) 1 0 0 +
    (tensorAt q (topVec q) 0 1 0 + tensorAt q (topVec q) 0 0 1) = _
  rw [top_at_100, top_at_zero_of_mode1, top_at_zero_of_mode2]
  all_goals simp

private lemma top_coeff_two : termCoeff (K := K) q (topVec q) 2 = 0 := by
  rw [termCoeff, anti_two]
  change tensorAt q (topVec q) 2 0 0 +
    (tensorAt q (topVec q) 1 1 0 +
      (tensorAt q (topVec q) 1 0 1 +
        (tensorAt q (topVec q) 0 2 0 +
          (tensorAt q (topVec q) 0 1 1 + tensorAt q (topVec q) 0 0 2)))) = 0
  rw [top_at_zero_of_mode0, top_at_zero_of_mode1, top_at_zero_of_mode2,
    top_at_zero_of_mode1, top_at_zero_of_mode1, top_at_zero_of_mode2]
  all_goals simp

private lemma top_coeff_three :
    termCoeff (K := K) q (topVec q) 3 =
      CWMonom K q (T q) (O q) (O q) +
      CWMonom K q (O q) (T q) (O q) +
      CWMonom K q (O q) (O q) (T q) := by
  rw [termCoeff, anti_three]
  change tensorAt q (topVec q) 3 0 0 +
    (tensorAt q (topVec q) 2 1 0 +
      (tensorAt q (topVec q) 2 0 1 +
        (tensorAt q (topVec q) 1 2 0 +
          (tensorAt q (topVec q) 1 1 1 +
            (tensorAt q (topVec q) 1 0 2 +
              (tensorAt q (topVec q) 0 3 0 +
                (tensorAt q (topVec q) 0 2 1 +
                  (tensorAt q (topVec q) 0 1 2 +
                    tensorAt q (topVec q) 0 0 3)))))))) = _
  rw [top_at_300, top_at_zero_of_mode0, top_at_zero_of_mode0,
    top_at_zero_of_mode1, top_at_zero_of_mode1, top_at_zero_of_mode2,
    top_at_030, top_at_zero_of_mode2, top_at_zero_of_mode1, top_at_003]
  · abel
  all_goals simp

private lemma coeff_zero : (Phi (K := K) q).coeff 0 = 0 := by
  rw [Phi_coeff_split]
  simp_rw [main_coeff_zero, sum_coeff_zero, top_coeff_zero]
  simp
  rfl

private lemma coeff_one : (Phi (K := K) q).coeff 1 = 0 := by
  rw [Phi_coeff_split]
  simp_rw [main_coeff_one, sum_coeff_one, top_coeff_one]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  simp [Nat.cast_smul_eq_nsmul]
  rfl

private lemma coeff_two : (Phi (K := K) q).coeff 2 = 0 := by
  rw [Phi_coeff_split]
  simp_rw [main_coeff_two, sum_coeff_two, top_coeff_two]
  abel

private lemma coeff_three : (Phi (K := K) q).coeff 3 = (CWObj K q).t := by
  rw [Phi_coeff_split]
  simp_rw [main_coeff_three, sum_coeff_three, top_coeff_three]
  change _ = CWTensor K q
  simp only [CWTensor, O, M, T]
  abel

theorem order_three :
    DegeneratesOfOrder (CWObj K q) (TensorObj.diagObj K 3 (q + 2)) 3 := by
  refine ⟨Phi q, ?_, coeff_three q⟩
  intro k hk
  have hk' : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  rcases hk' with rfl | rfl | rfl
  · exact coeff_zero q
  · exact coeff_one q
  · exact coeff_two q

end MME.CWBorderRank

open MME

/-- The Coppersmith--Winograd tensor has border rank at most `q+2`, over every field. -/
theorem solution {K : Type u} [Field K] (q : ℕ) :
    Degenerates (CWObj K q) (TensorObj.diagObj K 3 (q + 2)) := by
  exact ⟨3, CWBorderRank.order_three q⟩
