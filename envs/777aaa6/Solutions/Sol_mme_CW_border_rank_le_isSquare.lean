-- Prove2me | solution 1 for mme_CW_border_rank_le_isSquare
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:15:31.675089+00:00
-- url     : https://prove2.me/submissions/304225de-b458-4b05-a079-41bf804a7fc3

import Mathlib
import Definitions.Def_mme_CW_tensor
import Definitions.Def_mme_degeneration

set_option autoImplicit false

/-
Coppersmith and Winograd, Matrix multiplication via arithmetic progressions
(1990), p. 262, equation (10), multiplied by the parameter cubed.
There are q middle slots and two cancellation slots. Their coefficients below
degree three vanish, and their degree-three coefficient is the posted CW tensor.
The boundary slot omits a degree-four term in its first mode, which cannot affect
any coefficient used here. The construction works over every field.
-/

namespace CWBorder

open MME PiTensorProduct BigOperators Module

universe w
variable {K : Type w} [Field K]

noncomputable def basis (q : ℕ) : ∀ m : Fin 3, Basis (Fin (q + 2)) K (CWSpace K q m)
  | ⟨0, _⟩ => Pi.basisFun K (Fin (q + 2))
  | ⟨1, _⟩ => Pi.basisFun K (Fin (q + 2))
  | ⟨2, _⟩ => Pi.basisFun K (Fin (q + 2))

noncomputable def coord (q : ℕ) (p : Fin 3 → Fin (q + 2)) :
    PiTensorProduct K (CWSpace K q) →ₗ[K] K :=
  (Basis.piTensorProduct (basis q)).coord p

theorem coord_tprod (q : ℕ) (p : Fin 3 → Fin (q + 2)) (v : ∀ m, CWSpace K q m) :
    coord q p (tprod K v) = v 0 (p 0) * v 1 (p 1) * v 2 (p 2) := by
  simp [coord, Basis.coord_apply, Basis.piTensorProduct_repr_tprod_apply,
    Fin.prod_univ_succ, basis, mul_assoc]
  exact congrArg₂ (· * ·) (Pi.basisFun_repr K (Fin (q + 2)) (v 0) (p 0))
    (congrArg₂ (· * ·) (Pi.basisFun_repr K (Fin (q + 2)) (v 1) (p 1))
      (Pi.basisFun_repr K (Fin (q + 2)) (v 2) (p 2)))

theorem coord_ext (q : ℕ) (X Y : PiTensorProduct K (CWSpace K q))
    (h : ∀ p, coord q p X = coord q p Y) : X = Y := by
  apply (Basis.piTensorProduct (basis q)).repr.injective
  ext p
  exact h p

def O (q : ℕ) : Fin (q + 2) → K := Pi.single 0 1
def T (q : ℕ) : Fin (q + 2) → K := Pi.single ⟨q + 1, by omega⟩ 1
def M (q : ℕ) (i : Fin q) : Fin (q + 2) → K := Pi.single ⟨i.val + 1, by omega⟩ 1
def mid (q : ℕ) : Fin (q + 2) → K := ∑ i : Fin q, M q i

def middleVector (q : ℕ) (m : Fin 3) (d : ℕ) (i : Fin q) : Fin (q + 2) → K :=
  if m = 0 then
    if d = 1 then O q else if d = 2 then M q i else 0
  else if d = 0 then O q else if d = 1 then M q i else 0

def negativeVector (q : ℕ) (m : Fin 3) (d : ℕ) : Fin (q + 2) → K :=
  (if m = 0 then (-1 : K) else 1) •
    (if d = 0 then O q else if d = 2 then mid q else 0)

def boundaryVector (q : ℕ) (m : Fin 3) (d : ℕ) : Fin (q + 2) → K :=
  if d = 0 then O q else if m = 0 ∧ d = 1 then -(q : K) • O q
  else if d = 3 then T q else 0

def vector (q : ℕ) (m : Fin 3) (d : ℕ) : Fin (q + 2) → (Fin (q + 2) → K) :=
  Fin.addCases (middleVector q m d)
    (Fin.cases (negativeVector q m d) (fun _ => boundaryVector q m d))

noncomputable def coeffMap (q : ℕ) (d : ℕ) :
    ∀ m : Fin 3, (Fin (q + 2) → K) →ₗ[K] CWSpace K q m
  | ⟨0, _⟩ => (Pi.basisFun K (Fin (q + 2))).constr K (vector q 0 d)
  | ⟨1, _⟩ => (Pi.basisFun K (Fin (q + 2))).constr K (vector q 1 d)
  | ⟨2, _⟩ => (Pi.basisFun K (Fin (q + 2))).constr K (vector q 2 d)

noncomputable def family (q : ℕ) : PolyFamily (CWObj K q) (TensorObj.diagObj K 3 (q + 2)) where
  A m := Finsupp.single 0 (coeffMap q 0 m) + Finsupp.single 1 (coeffMap q 1 m) +
    Finsupp.single 2 (coeffMap q 2 m) + Finsupp.single 3 (coeffMap q 3 m)

theorem family_apply (q d : ℕ) (hd : d ≤ 3) (m : Fin 3) :
    (family q (K := K)).A m d = coeffMap q d m := by
  change (Finsupp.single 0 (coeffMap q 0 m) + Finsupp.single 1 (coeffMap q 1 m) +
    Finsupp.single 2 (coeffMap q 2 m) + Finsupp.single 3 (coeffMap q 3 m) :
      ℕ →₀ ((Fin (q + 2) → K) →ₗ[K] CWSpace K q m)) d = _
  interval_cases d <;> simp

theorem coord_map (q : ℕ) (p : Fin 3 → Fin (q + 2)) (d : Fin 3 → ℕ) :
    coord q p (PiTensorProduct.map (fun m => coeffMap q (d m) m)
      (TensorObj.diagObj K 3 (q + 2)).t) =
    ∑ s : Fin (q + 2), vector q 0 (d 0) s (p 0) * vector q 1 (d 1) s (p 1) *
      vector q 2 (d 2) s (p 2) := by
  simp only [TensorObj.diagObj, map_sum, PiTensorProduct.map_tprod, coord_tprod]
  apply Finset.sum_congr rfl
  intro s hs
  simp [coeffMap, Pi.single_apply]

def slotCoeff {q : ℕ} (g : Fin 3 → ℕ → (Fin (q + 2) → K)) (k : ℕ)
    (p : Fin 3 → Fin (q + 2)) : K :=
  ∑ d ∈ Finset.Nat.antidiagonalTuple 3 k, g 0 (d 0) (p 0) * g 1 (d 1) (p 1) * g 2 (d 2) (p 2)

theorem coord_coeff (q k : ℕ) (hk : k ≤ 3) (p : Fin 3 → Fin (q + 2)) :
    coord q p ((family q (K := K)).coeff k) =
      (∑ i : Fin q, slotCoeff (fun m d => middleVector q m d i) k p) +
      slotCoeff (negativeVector q) k p + slotCoeff (boundaryVector q) k p := by
  dsimp only [PolyFamily.coeff, CWObj, TensorObj.diagObj]
  rw [map_sum]
  have hsum : (∑ d ∈ Finset.Nat.antidiagonalTuple 3 k,
      coord q p ((PiTensorProduct.map (fun m => (family q).A m (d m)))
        (TensorObj.diagObj K 3 (q + 2)).t)) =
      ∑ d ∈ Finset.Nat.antidiagonalTuple 3 k, ∑ s : Fin (q + 2),
        vector q 0 (d 0) s (p 0) * vector q 1 (d 1) s (p 1) * vector q 2 (d 2) s (p 2) := by
    apply Finset.sum_congr rfl
    intro d hd
    have hdle : ∀ m, d m ≤ 3 := by
      intro m
      have hs := Finset.Nat.mem_antidiagonalTuple.mp hd
      have hm : d m ≤ ∑ i, d i := Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_univ m)
      omega
    simp only [family_apply q _ (hdle _)]
    exact coord_map q p d
  trans ∑ d ∈ Finset.Nat.antidiagonalTuple 3 k, ∑ s : Fin (q + 2),
    vector q 0 (d 0) s (p 0) * vector q 1 (d 1) s (p 1) * vector q 2 (d 2) s (p 2)
  · exact hsum
  rw [Finset.sum_comm, Fin.sum_univ_add]
  simp [slotCoeff, vector, Fin.sum_univ_two, add_assoc]
  rfl

theorem anti0 : Finset.Nat.antidiagonalTuple 3 0 = {![0, 0, 0]} := by decide
theorem anti1 : Finset.Nat.antidiagonalTuple 3 1 = {![0, 0, 1], ![0, 1, 0], ![1, 0, 0]} := by decide
theorem anti2 : Finset.Nat.antidiagonalTuple 3 2 =
    {![0, 0, 2], ![0, 1, 1], ![0, 2, 0], ![1, 0, 1], ![1, 1, 0], ![2, 0, 0]} := by decide
theorem anti3 : Finset.Nat.antidiagonalTuple 3 3 =
    {![0, 0, 3], ![0, 1, 2], ![0, 2, 1], ![0, 3, 0], ![1, 0, 2], ![1, 1, 1],
      ![1, 2, 0], ![2, 0, 1], ![2, 1, 0], ![3, 0, 0]} := by decide

theorem slot_middle_zero (q : ℕ) (i : Fin q) (p : Fin 3 → Fin (q + 2)) :
    slotCoeff (fun m d => middleVector q m d i (K := K)) 0 p = 0 := by
  simp [slotCoeff, anti0, middleVector]

theorem slot_middle_one (q : ℕ) (i : Fin q) (p : Fin 3 → Fin (q + 2)) :
    slotCoeff (fun m d => middleVector q m d i (K := K)) 1 p =
      O q (p 0) * O q (p 1) * O q (p 2) := by
  simp [slotCoeff, anti1, middleVector]

theorem slot_middle_two (q : ℕ) (i : Fin q) (p : Fin 3 → Fin (q + 2)) :
    slotCoeff (fun m d => middleVector q m d i (K := K)) 2 p =
      O q (p 0) * O q (p 1) * M q i (p 2) +
      O q (p 0) * M q i (p 1) * O q (p 2) + M q i (p 0) * O q (p 1) * O q (p 2) := by
  simp [slotCoeff, anti2, middleVector, add_assoc]

theorem slot_middle_three (q : ℕ) (i : Fin q) (p : Fin 3 → Fin (q + 2)) :
    slotCoeff (fun m d => middleVector q m d i (K := K)) 3 p =
      O q (p 0) * M q i (p 1) * M q i (p 2) +
      M q i (p 0) * O q (p 1) * M q i (p 2) + M q i (p 0) * M q i (p 1) * O q (p 2) := by
  simp [slotCoeff, anti3, middleVector, add_assoc]

theorem slot_negative_zero (q : ℕ) (p : Fin 3 → Fin (q + 2)) :
    slotCoeff (negativeVector q (K := K)) 0 p =
      -(O q (p 0) * O q (p 1) * O q (p 2)) := by
  simp [slotCoeff, anti0, negativeVector]

theorem slot_negative_one (q : ℕ) (p : Fin 3 → Fin (q + 2)) :
    slotCoeff (negativeVector q (K := K)) 1 p = 0 := by
  simp [slotCoeff, anti1, negativeVector]

theorem slot_negative_two (q : ℕ) (p : Fin 3 → Fin (q + 2)) :
    slotCoeff (negativeVector q (K := K)) 2 p =
      -(O q (p 0) * O q (p 1) * mid q (p 2) +
        O q (p 0) * mid q (p 1) * O q (p 2) + mid q (p 0) * O q (p 1) * O q (p 2)) := by
  simp [slotCoeff, anti2, negativeVector]
  ring

theorem slot_negative_three (q : ℕ) (p : Fin 3 → Fin (q + 2)) :
    slotCoeff (negativeVector q (K := K)) 3 p = 0 := by
  simp [slotCoeff, anti3, negativeVector]

theorem slot_boundary_zero (q : ℕ) (p : Fin 3 → Fin (q + 2)) :
    slotCoeff (boundaryVector q (K := K)) 0 p = O q (p 0) * O q (p 1) * O q (p 2) := by
  simp [slotCoeff, anti0, boundaryVector]

theorem slot_boundary_one (q : ℕ) (p : Fin 3 → Fin (q + 2)) :
    slotCoeff (boundaryVector q (K := K)) 1 p = -(q : K) * O q (p 0) * O q (p 1) * O q (p 2) := by
  simp [slotCoeff, anti1, boundaryVector]

theorem slot_boundary_two (q : ℕ) (p : Fin 3 → Fin (q + 2)) :
    slotCoeff (boundaryVector q (K := K)) 2 p = 0 := by
  simp [slotCoeff, anti2, boundaryVector]

theorem slot_boundary_three (q : ℕ) (p : Fin 3 → Fin (q + 2)) :
    slotCoeff (boundaryVector q (K := K)) 3 p =
      O q (p 0) * O q (p 1) * T q (p 2) + O q (p 0) * T q (p 1) * O q (p 2) +
        T q (p 0) * O q (p 1) * O q (p 2) := by
  simp [slotCoeff, anti3, boundaryVector, add_assoc]

theorem coord_CWTensor (q : ℕ) (p : Fin 3 → Fin (q + 2)) :
    coord q p (CWTensor K q) =
      (∑ i : Fin q, (O q (p 0) * M q i (p 1) * M q i (p 2) +
        M q i (p 0) * O q (p 1) * M q i (p 2) + M q i (p 0) * M q i (p 1) * O q (p 2))) +
      O q (p 0) * O q (p 1) * T q (p 2) + O q (p 0) * T q (p 1) * O q (p 2) +
        T q (p 0) * O q (p 1) * O q (p 2) := by
  simp [CWTensor, CWMonom, coord_tprod, O, M, T]

theorem coeff_zero (q : ℕ) : (family q (K := K)).coeff 0 = 0 := by
  apply coord_ext q
  intro p
  change coord q p ((family q).coeff 0) = coord q p (0 : PiTensorProduct K (CWSpace K q))
  rw [map_zero, coord_coeff q 0 (by omega)]
  simp [slot_middle_zero, slot_negative_zero, slot_boundary_zero]

theorem coeff_one (q : ℕ) : (family q (K := K)).coeff 1 = 0 := by
  apply coord_ext q
  intro p
  change coord q p ((family q).coeff 1) = coord q p (0 : PiTensorProduct K (CWSpace K q))
  rw [map_zero, coord_coeff q 1 (by omega)]
  simp [slot_middle_one, slot_negative_one, slot_boundary_one, nsmul_eq_mul]
  ring

theorem coeff_two (q : ℕ) : (family q (K := K)).coeff 2 = 0 := by
  apply coord_ext q
  intro p
  change coord q p ((family q).coeff 2) = coord q p (0 : PiTensorProduct K (CWSpace K q))
  rw [map_zero, coord_coeff q 2 (by omega)]
  simp [slot_middle_two, slot_negative_two, slot_boundary_two, mid,
    Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]

theorem coeff_three (q : ℕ) : (family q (K := K)).coeff 3 = CWTensor K q := by
  apply coord_ext q
  intro p
  rw [coord_coeff q 3 (by omega), coord_CWTensor]
  simp [slot_middle_three, slot_negative_three, slot_boundary_three, add_assoc]

theorem degenerates (q : ℕ) : Degenerates (CWObj K q) (TensorObj.diagObj K 3 (q + 2)) := by
  refine ⟨3, family q, ?_, ?_⟩
  · intro k hk
    interval_cases k
    · exact coeff_zero q
    · exact coeff_one q
    · exact coeff_two q
  · exact coeff_three q

end CWBorder

open MME
universe cw_u

theorem solution {K : Type cw_u} [Field K] (q : ℕ)
    (_hSq : IsSquare ((q + 1 : ℕ) : K)) :
    Degenerates (CWObj K q) (TensorObj.diagObj K 3 (q + 2)) :=
  CWBorder.degenerates q
