-- Prove2me | solution 1 for LinearOptimization.farkas_inequality_form_fintype
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-05T21:03:14.421382+00:00
-- url     : https://prove2.me/submissions/42dd1028-b048-4ec0-b857-fe5e701edaeb

import Theorems.Thm_LinearOptimization_farkas_inequality_form

open Matrix

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (A : Matrix ι (Fin n) ℝ) (b : ι → ℝ) (c : Fin n → ℝ) (d : ℝ)
    (hfeas : ∃ x : Fin n → ℝ, A.mulVec x ≤ b) :
    (∀ x : Fin n → ℝ, A.mulVec x ≤ b → c ⬝ᵥ x ≤ d) ↔
      ∃ p : ι → ℝ, 0 ≤ p ∧ Aᵀ.mulVec p = c ∧ p ⬝ᵥ b ≤ d := by
  classical
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let A' : Matrix (Fin (Fintype.card ι)) (Fin n) ℝ := fun i j ↦ A (e.symm i) j
  let b' : Fin (Fintype.card ι) → ℝ := fun i ↦ b (e.symm i)
  have hrow (x : Fin n → ℝ) : A'.mulVec x ≤ b' ↔ A.mulVec x ≤ b := by
    constructor
    · intro h i
      simpa [A', b', Matrix.mulVec] using h (e i)
    · intro h i
      simpa [A', b', Matrix.mulVec] using h (e.symm i)
  have hfeas' : ∃ x : Fin n → ℝ, A'.mulVec x ≤ b' := by
    rcases hfeas with ⟨x, hx⟩
    exact ⟨x, (hrow x).2 hx⟩
  constructor
  · intro hall
    have hall' : ∀ x : Fin n → ℝ, A'.mulVec x ≤ b' → c ⬝ᵥ x ≤ d :=
      fun x hx ↦ hall x ((hrow x).1 hx)
    rcases (LinearOptimization.farkas_inequality_form A' b' c d hfeas').mp hall' with
      ⟨p', hp', hA', hb'⟩
    let p : ι → ℝ := fun i ↦ p' (e i)
    refine ⟨p, fun i ↦ hp' (e i), ?_, ?_⟩
    · funext j
      have hj := congrFun hA' j
      change (∑ i : ι, A i j * p' (e i)) = c j
      calc
        (∑ i : ι, A i j * p' (e i)) =
            ∑ r : Fin (Fintype.card ι), A (e.symm r) j * p' r := by
          simpa using e.sum_comp (fun r ↦ A (e.symm r) j * p' r)
        _ = c j := by simpa [A', Matrix.mulVec] using hj
    · simpa [b', p, dotProduct, ← e.sum_comp] using hb'
  · rintro ⟨p, hp, hA, hb⟩
    let p' : Fin (Fintype.card ι) → ℝ := fun i ↦ p (e.symm i)
    have hp'witness :
        ∃ p' : Fin (Fintype.card ι) → ℝ,
          0 ≤ p' ∧ A'ᵀ.mulVec p' = c ∧ p' ⬝ᵥ b' ≤ d := by
      refine ⟨p', fun i ↦ hp (e.symm i), ?_, ?_⟩
      · funext j
        have hj := congrFun hA j
        change (∑ r : Fin (Fintype.card ι),
          A (e.symm r) j * p (e.symm r)) = c j
        calc
          (∑ r : Fin (Fintype.card ι), A (e.symm r) j * p (e.symm r)) =
              ∑ i : ι, A i j * p i := by
            simpa using e.symm.sum_comp (fun i ↦ A i j * p i)
          _ = c j := by simpa [Matrix.mulVec] using hj
      · simpa [b', p', dotProduct, ← e.sum_comp] using hb
    have hall' :=
      (LinearOptimization.farkas_inequality_form A' b' c d hfeas').mpr hp'witness
    intro x hx
    exact hall' x ((hrow x).2 hx)
