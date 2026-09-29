-- Prove2me | solution 1 for mme_released_116_child_tensor_partition
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T01:30:49.457505+00:00
-- url     : https://prove2.me/submissions/316dc12b-88d4-4388-9dd1-a37724a83380

import Definitions.Def_mme_released_116_integer_profiles
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Theorems.Thm_mme_toQ_kronFin
universe u

open MME MME.RecursiveYZ MME.Released116
set_option autoImplicit false

private def boundarySplit (i : Fin 3) : Split :=
  if i = 0 then ⟨![0, 0, 4], by decide⟩
  else if i = 1 then ⟨![0, 1, 3], by decide⟩
  else ⟨![1, 0, 3], by decide⟩

private def partitionCell : Fin 18 ⊕ Fin 6 → Cell 4 6 parent
  | .inl i => ⟨(finProdFinEquiv.symm i : Fin 6 × Fin 3).1,
      boundarySplit (finProdFinEquiv.symm i : Fin 6 × Fin 3).2⟩
  | .inr r => ⟨r, ⟨![1, 1, 2], by change _ ∧ ∀ i, _ ≤ (![1, 1, 6] : Fin 3 → ℕ) i; decide⟩⟩

private theorem cell_eq_iff (x y : Cell 4 6 parent) :
    x = y ↔ x.1 = y.1 ∧ ∀ i, (x.2.val i).val = (y.2.val i).val := by
  constructor
  · rintro rfl
    exact ⟨rfl, fun _ ↦ rfl⟩
  · rcases x with ⟨r, x⟩
    rcases y with ⟨s, y⟩
    rintro ⟨hrs, hval⟩
    dsimp only at hrs hval
    subst s
    congr 1
    apply Subtype.ext
    funext i
    exact Fin.ext (hval i)

private theorem partitionCell_bijective : Function.Bijective partitionCell := by
  unfold Function.Bijective Function.Injective Function.Surjective
  simp only [cell_eq_iff]
  decide +kernel

/-- The full released child index consists of eighteen boundary cells and
six interior 112 cells. The equivalence retains each physical cell once. -/
private theorem mme_released_116_child_partition :
    ∃ e : (Fin 18 ⊕ Fin 6) ≃ Cell 4 6 parent,
      (∀ i : Fin 18, ∃ z : Fin 3, ((e (.inl i)).2.val z).val = 0) ∧
      (∀ r : Fin 6, e (.inr r) = ⟨r, ⟨![1, 1, 2], by change _ ∧ ∀ i, _ ≤ (![1, 1, 6] : Fin 3 → ℕ) i; decide⟩⟩) := by
  refine ⟨Equiv.ofBijective partitionCell partitionCell_bijective, ?_, ?_⟩
  · change ∀ i : Fin 18, ∃ z : Fin 3, ((partitionCell (.inl i)).2.val z).val = 0
    decide +kernel
  · intro r
    rfl



open MME BigOperators
set_option autoImplicit false

/-- A partition of the finite factor index gives an actual tensor
isomorphism to the Kronecker product of the two indexed subproducts. -/
private theorem mme_kronFin_partition_isomorphic {K : Type u} [Field K] {a b : ℕ}
    (e : (Fin a ⊕ Fin b) ≃ Fin (a + b)) (T : Fin (a + b) → TensorObj K 3) :
    TensorObj.Isomorphic (TensorObj.kronFin (a + b) T)
      (TensorObj.kron
        (TensorObj.kronFin a (fun i ↦ T (e (.inl i))))
        (TensorObj.kronFin b (fun i ↦ T (e (.inr i))))) := by
  rw [← TensorQ.toQ_eq_iff]
  simp only [TensorQ.toQ_kron, mme_toQ_kronFin]
  rw [← Equiv.prod_comp e (fun i ↦ TensorQ.toQ (T i)), Fintype.prod_sum_type]


/-- The released full child tensor splits into its eighteen boundary factors
and six canonical 112 factors, independently of the original enumeration. -/
theorem solution :
    ∃ e : (Fin 18 ⊕ Fin 6) ≃ Cell 4 6 parent,
      (∀ i : Fin 18, ∃ z : Fin 3, ((e (.inl i)).2.val z).val = 0) ∧
      (∀ r : Fin 6, e (.inr r) = ⟨r, ⟨![1, 1, 2], by
        change _ ∧ ∀ i, _ ≤ (![1, 1, 6] : Fin 3 → ℕ) i
        decide⟩⟩) ∧
      ∀ (d : Fin 24 ≃ Cell 4 6 parent) (K : Type u) [Field K]
        (T : Cell 4 6 parent → TensorObj K 3),
        TensorObj.Isomorphic (TensorObj.kronFin 24 (fun i ↦ T (d i)))
          (TensorObj.kron
            (TensorObj.kronFin 18 (fun i ↦ T (e (.inl i))))
            (TensorObj.kronFin 6 (fun r ↦ T ⟨r, ⟨![1, 1, 2], by
              change _ ∧ ∀ i, _ ≤ (![1, 1, 6] : Fin 3 → ℕ) i
              decide⟩⟩))) := by
  obtain ⟨e, hb, hi⟩ := mme_released_116_child_partition
  refine ⟨e, hb, hi, ?_⟩
  intro d K _ T
  have h := mme_kronFin_partition_isomorphic (K := K) (e.trans d.symm)
    (fun i ↦ T (d i))
  simpa only [Equiv.trans_apply, Equiv.apply_symm_apply, hi] using h


#print axioms solution
