-- Prove2me | solution 1 for mme_released_116_full_child_weight_assembly
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T01:32:41.976649+00:00
-- url     : https://prove2.me/submissions/35b7e082-f380-4499-8609-3d1e17d07255

import Definitions.Def_mme_released_116_integer_profiles
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Theorems.Thm_mme_toQ_kronFin
import Definitions.Def_mme_rank_bridge
import Definitions.Def_mme_mmobj_mul
import Definitions.Def_mme_cyclicSymmetrization_public_perm
import Definitions.Def_mme_six_symmetrized_tau_value
import Theorems.Thm_mme_sixSymmetrization_restrict
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
private theorem mme_released_116_child_tensor_partition :
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


open MME BigOperators
set_option autoImplicit false

private theorem kron_restrict_for_tau_product
    {K : Type u} [Field K] {d : ℕ} (hd : 1 < d)
    {X X' Y Y' : TensorObj K d}
    (hX : TensorObj.Restrict X X')
    (hY : TensorObj.Restrict Y Y') :
    TensorObj.Restrict (TensorObj.kron X Y) (TensorObj.kron X' Y') := by
  rw [← TensorQ.le_toQ]
  let P := TensorQ.tensorStrassen K d hd
  have hx : P.le (TensorQ.toQ X) (TensorQ.toQ X') := hX
  have hy : P.le (TensorQ.toQ Y) (TensorQ.toQ Y') := hY
  have hleft :
      P.le (TensorQ.toQ X * TensorQ.toQ Y)
        (TensorQ.toQ X' * TensorQ.toQ Y) :=
    P.mul_right _ _ hx _
  have hright :
      P.le (TensorQ.toQ X' * TensorQ.toQ Y)
        (TensorQ.toQ X' * TensorQ.toQ Y') := by
    simpa only [mul_comm] using P.mul_right _ _ hy (TensorQ.toQ X')
  exact P.le_trans _ _ _ hleft hright


private theorem six_kron_iso {K : Type u} [Field K] (X Y : TensorObj K 3) :
    TensorObj.Isomorphic
      (TensorObj.kron (sixSymmetrization X) (sixSymmetrization Y))
      (sixSymmetrization (TensorObj.kron X Y)) := by
  rw [← TensorQ.toQ_eq_iff]
  simp only [sixSymmetrization, cyclicSymmetrization_eq_public_perm,
    TensorQ.toQ_kron, ← TensorQ.permAut_toQ, map_mul]
  ring

/-- A square boundary extraction multiplies every interior matrix dimension
without changing the number of summands or losing exponential weight. -/
private theorem mme_six_square_family_product_weight
    {K : Type u} [Field K] {X Y : TensorObj K 3} {q : ℕ}
    (M : ℕ) (a b c : Fin q → ℕ) (tau boundaryRate interiorRate : ℝ)
    (hboundary : TensorObj.Restrict (MMObj K M M M) (sixSymmetrization X))
    (hinterior : TensorObj.Restrict
      (TensorObj.bigAdd (fun i ↦ MMObj K (a i) (b i) (c i))) (sixSymmetrization Y))
    (hboundaryWeight : Real.exp boundaryRate ≤ ((M * M * M : ℕ) : ℝ) ^ tau)
    (hinteriorWeight : Real.exp interiorRate ≤
      ∑ i, ((a i * b i * c i : ℕ) : ℝ) ^ tau) :
    TensorObj.Restrict
      (TensorObj.bigAdd (fun i ↦ MMObj K (M * a i) (M * b i) (M * c i)))
      (sixSymmetrization (TensorObj.kron X Y)) ∧
    Real.exp (boundaryRate + interiorRate) ≤
      ∑ i, (((M * a i) * (M * b i) * (M * c i) : ℕ) : ℝ) ^ tau := by
  have hdist : TensorObj.Isomorphic
      (TensorObj.bigAdd (fun i ↦ MMObj K (M * a i) (M * b i) (M * c i)))
      (TensorObj.kron (MMObj K M M M)
        (TensorObj.bigAdd (fun i ↦ MMObj K (a i) (b i) (c i)))) := by
    rw [← TensorQ.toQ_eq_iff, TensorQ.toQ_kron, TensorQ.toQ_bigAdd,
      TensorQ.toQ_bigAdd, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact (TensorQ.toQ_eq_iff.mpr (MMObj_kron_iso (K := K)
      M M M (a i) (b i) (c i))).symm.trans (TensorQ.toQ_kron _ _)
  constructor
  · exact hdist.1.trans ((kron_restrict_for_tau_product (by decide)
      hboundary hinterior).trans (six_kron_iso X Y).1)
  · rw [Real.exp_add]
    have hmul := mul_le_mul hboundaryWeight hinteriorWeight
      (Real.exp_pos interiorRate).le (Real.rpow_nonneg (by positivity) tau)
    calc
      Real.exp boundaryRate * Real.exp interiorRate ≤
          ((M * M * M : ℕ) : ℝ) ^ tau *
            ∑ i, ((a i * b i * c i : ℕ) : ℝ) ^ tau := hmul
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [← Real.mul_rpow (by positivity) (by positivity)]
        congr 1
        push_cast
        ring


/-- Boundary and interior extraction weights combine on the full released
child tensor, preserving the interior summands and every physical child factor. -/
theorem solution :
    ∃ e : (Fin 18 ⊕ Fin 6) ≃ Cell 4 6 parent,
      (∀ i : Fin 18, ∃ z : Fin 3, ((e (.inl i)).2.val z).val = 0) ∧
      (∀ r : Fin 6, e (.inr r) = ⟨r, ⟨![1, 1, 2], by
        change _ ∧ ∀ i, _ ≤ (![1, 1, 6] : Fin 3 → ℕ) i
        decide⟩⟩) ∧
      ∀ (d : Fin 24 ≃ Cell 4 6 parent) (K : Type u) [Field K]
        (T : Cell 4 6 parent → TensorObj K 3) (q M : ℕ)
        (a b c : Fin q → ℕ) (tau boundaryRate interiorRate : ℝ),
        TensorObj.Restrict (MMObj K M M M)
          (sixSymmetrization (TensorObj.kronFin 18 (fun i ↦ T (e (.inl i))))) →
        TensorObj.Restrict
          (TensorObj.bigAdd (fun i ↦ MMObj K (a i) (b i) (c i)))
          (sixSymmetrization (TensorObj.kronFin 6 (fun r ↦ T ⟨r, ⟨![1, 1, 2], by
            change _ ∧ ∀ i, _ ≤ (![1, 1, 6] : Fin 3 → ℕ) i
            decide⟩⟩))) →
        Real.exp boundaryRate ≤ ((M * M * M : ℕ) : ℝ) ^ tau →
        Real.exp interiorRate ≤ ∑ i, ((a i * b i * c i : ℕ) : ℝ) ^ tau →
        TensorObj.Restrict
          (TensorObj.bigAdd (fun i ↦ MMObj K (M * a i) (M * b i) (M * c i)))
          (sixSymmetrization (TensorObj.kronFin 24 (fun i ↦ T (d i)))) ∧
        Real.exp (boundaryRate + interiorRate) ≤
          ∑ i, (((M * a i) * (M * b i) * (M * c i) : ℕ) : ℝ) ^ tau := by
  obtain ⟨e, hb, hi, hpartition⟩ := mme_released_116_child_tensor_partition.{u}
  refine ⟨e, hb, hi, ?_⟩
  intro d K _ T q M a b c tau boundaryRate interiorRate hboundary hinterior hwB hwI
  obtain ⟨hextract, hweight⟩ := mme_six_square_family_product_weight
    M a b c tau boundaryRate interiorRate hboundary hinterior hwB hwI
  exact ⟨hextract.trans (mme_sixSymmetrization_restrict (hpartition d K T).2), hweight⟩


#print axioms solution
