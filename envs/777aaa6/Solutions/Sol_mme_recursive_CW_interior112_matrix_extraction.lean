-- Prove2me | solution 1 for mme_recursive_CW_interior112_matrix_extraction
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T10:31:53.842125+00:00
-- url     : https://prove2.me/submissions/9b62f9bd-1953-4cc3-908a-8fb142349d01

import Theorems.Thm_mme_recursive_CW_unbroken_matrix_extraction_of_joint_histogram

open BigOperators MME MME.TensorObj MME.CompleteSplit MME.RecursiveYZ
  MME.RecursiveYZ.CWCells
open scoped Classical

private def atoms112 : Fin 4 → Fin 3 → CompleteWord 2 :=
  ![![![1, 0], ![1, 0], ![0, 2]],
    ![![1, 0], ![0, 1], ![1, 1]],
    ![![0, 1], ![1, 0], ![1, 1]],
    ![![0, 1], ![0, 1], ![2, 0]]]

private theorem atomic_sum {T V : Type*} [Fintype T] [Fintype V] [DecidableEq V]
    (atom : T → V) (weight : T → ℕ) (f : V → ℕ) :
    (∑ v, (∑ t, if atom t = v then weight t else 0) * f v) =
      ∑ t, weight t * f (atom t) := by
  classical
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp [ite_mul]

private theorem atomic_marginal {T V W : Type*} [Fintype T] [Fintype V]
    [DecidableEq V] [DecidableEq W]
    (atom : T → V) (weight : T → ℕ) (proj : V → W) (s : W) :
    (∑ v, if proj v = s then (∑ t, if atom t = v then weight t else 0) else 0) =
      ∑ t, if proj (atom t) = s then weight t else 0 := by
  have h := atomic_sum atom weight (fun v ↦ if proj v = s then 1 else 0)
  simpa only [mul_ite, mul_one, mul_zero] using h

private theorem atoms112_grade (t : Fin 4) (i : Fin 3) :
    grade (atoms112 t i) = (![1, 1, 2] : Fin 3 → ℕ) i := by
  fin_cases t <;> fin_cases i <;> decide

private theorem atoms112_support (t : Fin 4) (r : Fin 2) :
    (atoms112 t 0 r).val + (atoms112 t 1 r).val + (atoms112 t 2 r).val = 2 := by
  fin_cases t <;> fin_cases r <;> decide

private theorem atoms112_pair02 (t : Fin 4) :
    (Finset.univ.filter (fun r ↦ (atoms112 t 0 r).val = 1 ∧
      (atoms112 t 2 r).val = 1)).card = (![0, 1, 1, 0] : Fin 4 → ℕ) t := by
  fin_cases t <;> decide

private theorem atoms112_pair01 (t : Fin 4) :
    (Finset.univ.filter (fun r ↦ (atoms112 t 0 r).val = 1 ∧
      (atoms112 t 1 r).val = 1)).card = (![1, 0, 0, 1] : Fin 4 → ℕ) t := by
  fin_cases t <;> decide

private theorem atoms112_pair12 (t : Fin 4) :
    (Finset.univ.filter (fun r ↦ (atoms112 t 1 r).val = 1 ∧
      (atoms112 t 2 r).val = 1)).card = (![0, 1, 1, 0] : Fin 4 → ℕ) t := by
  fin_cases t <;> decide

/-- Four integer counts give explicit marginals and a matrix restriction in the (1,1,2) block. -/
theorem interior112_matrix_extraction {K : Type*} [Field K] (a b c d : ℕ) :
    let mu : Fin 3 → CompleteWord 2 → ℕ :=
      ![fun s ↦ (if s = ![1, 0] then a + b else 0) +
          (if s = ![0, 1] then c + d else 0),
        fun s ↦ (if s = ![1, 0] then a + c else 0) +
          (if s = ![0, 1] then b + d else 0),
        fun s ↦ (if s = ![0, 2] then a else 0) +
          (if s = ![1, 1] then b + c else 0) + (if s = ![2, 0] then d else 0)]
    Restrict (MMObj K (5 ^ (b + c)) (5 ^ (a + d)) (5 ^ (b + c)))
      (unbroken K 5 2 (a + b + c + d) (Equiv.refl _) (fun _ ↦ Unit.unit)
        (fun _ ↦ ![1, 1, 2]) (fun i _ ↦ mu i)) := by
  classical
  dsimp only
  let wt : Fin 4 → ℕ := ![a, b, c, d]
  let joint (v : Fin 3 → CompleteWord 2) := ∑ t, if atoms112 t = v then wt t else 0
  have hm : ∑ v, joint v = a + b + c + d := by
    have h := atomic_sum atoms112 wt (fun _ ↦ 1)
    simpa [joint, wt, Fin.sum_univ_succ, add_assoc] using h
  have hmarg (i : Fin 3) (s : CompleteWord 2) :
      (∑ v, if v i = s then joint v else 0) =
        ∑ t, if atoms112 t i = s then wt t else 0 := by
    exact atomic_marginal atoms112 wt (fun v ↦ v i) s
  have hmem (v : Fin 3 → CompleteWord 2) (hv : 0 < joint v) :
      ∃ t, atoms112 t = v := by
    obtain ⟨t, _, ht⟩ := Finset.sum_pos_iff.mp hv
    by_cases he : atoms112 t = v
    · exact ⟨t, he⟩
    · simp [he] at ht
  have h := mme_recursive_CW_unbroken_matrix_extraction_of_joint_histogram
    (K := K) (ell := 2) (Equiv.refl (Fin (a + b + c + d))) (fun _ ↦ Unit.unit)
    (fun _ ↦ ![1, 1, 2]) (fun i _ s ↦ ∑ t, if atoms112 t i = s then wt t else 0)
    (fun _ ↦ joint) (by intro u; simpa using hm)
    (fun i _ s ↦ hmarg i s)
    (by intro u v hv i; obtain ⟨t, rfl⟩ := hmem v hv; exact atoms112_grade t i)
    (by intro u v hv r; obtain ⟨t, rfl⟩ := hmem v hv; exact atoms112_support t r)
  have hn (i k : Fin 3) := atomic_sum atoms112 wt (fun v ↦
    (Finset.univ.filter (fun r ↦ (v i r).val = 1 ∧ (v k r).val = 1)).card)
  have h02 : (∑ v, joint v * (Finset.univ.filter (fun r ↦
      (v 0 r).val = 1 ∧ (v 2 r).val = 1)).card) = b + c := by
    rw [show (∑ v, joint v * (Finset.univ.filter (fun r ↦
      (v 0 r).val = 1 ∧ (v 2 r).val = 1)).card) = _ from hn 0 2]
    simp only [atoms112_pair02]
    simp [wt, Fin.sum_univ_succ]
  have h01 : (∑ v, joint v * (Finset.univ.filter (fun r ↦
      (v 0 r).val = 1 ∧ (v 1 r).val = 1)).card) = a + d := by
    rw [show (∑ v, joint v * (Finset.univ.filter (fun r ↦
      (v 0 r).val = 1 ∧ (v 1 r).val = 1)).card) = _ from hn 0 1]
    simp only [atoms112_pair01]
    simp [wt, Fin.sum_univ_succ]
  have h12 : (∑ v, joint v * (Finset.univ.filter (fun r ↦
      (v 1 r).val = 1 ∧ (v 2 r).val = 1)).card) = b + c := by
    rw [show (∑ v, joint v * (Finset.univ.filter (fun r ↦
      (v 1 r).val = 1 ∧ (v 2 r).val = 1)).card) = _ from hn 1 2]
    simp only [atoms112_pair12]
    simp [wt, Fin.sum_univ_succ]
  simp only [Fintype.sum_unique] at h
  rw [h02, h01, h12] at h
  have hmu : (fun i (_ : Unit) s ↦ ∑ t, if atoms112 t i = s then wt t else 0) =
      (fun i (_ : Unit) ↦ (
      ![fun s ↦ (if s = ![1, 0] then a + b else 0) +
          (if s = ![0, 1] then c + d else 0),
        fun s ↦ (if s = ![1, 0] then a + c else 0) +
          (if s = ![0, 1] then b + d else 0),
        fun s ↦ (if s = ![0, 2] then a else 0) +
          (if s = ![1, 1] then b + c else 0) + (if s = ![2, 0] then d else 0)] : Fin 3 → CompleteWord 2 → ℕ) i) := by
    funext i u s
    fin_cases i <;> simp only [atoms112, wt, Fin.sum_univ_succ,
      Finset.univ_eq_empty, Finset.sum_empty, add_zero, Matrix.cons_val_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ, Matrix.cons_val_succ', eq_comm]
    all_goals split_ifs <;> omega
  rw [hmu] at h
  exact h


theorem solution {K : Type*} [Field K] (a b c d : ℕ) :
    let mu : Fin 3 → CompleteWord 2 → ℕ :=
      ![fun s ↦ (if s = ![1, 0] then a + b else 0) +
          (if s = ![0, 1] then c + d else 0),
        fun s ↦ (if s = ![1, 0] then a + c else 0) +
          (if s = ![0, 1] then b + d else 0),
        fun s ↦ (if s = ![0, 2] then a else 0) +
          (if s = ![1, 1] then b + c else 0) + (if s = ![2, 0] then d else 0)]
    Restrict (MMObj K (5 ^ (b + c)) (5 ^ (a + d)) (5 ^ (b + c)))
      (unbroken K 5 2 (a + b + c + d) (Equiv.refl _) (fun _ ↦ Unit.unit)
        (fun _ ↦ ![1, 1, 2]) (fun i _ ↦ mu i)) := by
  exact interior112_matrix_extraction a b c d
#print axioms solution
