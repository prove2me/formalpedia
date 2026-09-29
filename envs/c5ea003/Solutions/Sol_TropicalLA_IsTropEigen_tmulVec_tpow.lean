-- Prove2me | solution 1 for TropicalLA.IsTropEigen.tmulVec_tpow
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T00:27:58.274815+00:00
-- url     : https://prove2.me/submissions/2757ab26-1fe0-4ecf-ab30-fa00a1b0fac4

import Mathlib
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalEigenvalue
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalGelfand
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalMatrix
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalPerronFrobenius
open TropicalLA in
theorem solution {ι : Type*} [Fintype ι] [Nonempty ι] {A : Matrix ι ι ℝ} {lam : ℝ}
    {v : ι → ℝ} (h : IsTropEigen A lam v) (m : ℕ) :
    tmulVec (tpow A m) v = fun i => (m + 1) * lam + v i := by
  -- the tropical action is associative: `(B ⊗ C) ⊗ w = B ⊗ (C ⊗ w)`
  have hassoc : ∀ (B C : Matrix ι ι ℝ) (w : ι → ℝ),
      tmulVec (tmul B C) w = tmulVec B (tmulVec C w) := by
    intro B C w
    funext i
    simp only [tmulVec, tmul]
    apply le_antisymm
    · refine Finset.sup'_le _ _ fun j _ => ?_
      obtain ⟨k, -, hk⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
        (fun k => B i k + C k j)
      rw [hk]
      calc B i k + C k j + w j
          = B i k + (C k j + w j) := by ring
        _ ≤ B i k + Finset.univ.sup' Finset.univ_nonempty (fun j' => C k j' + w j') := by
            have := Finset.le_sup' (fun j' => C k j' + w j') (Finset.mem_univ j)
            linarith
        _ ≤ _ := Finset.le_sup' (fun k => B i k +
              Finset.univ.sup' Finset.univ_nonempty (fun j' => C k j' + w j')) (Finset.mem_univ k)
    · refine Finset.sup'_le _ _ fun k _ => ?_
      obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
        (fun j => C k j + w j)
      rw [hj]
      calc B i k + (C k j + w j)
          = B i k + C k j + w j := by ring
        _ ≤ Finset.univ.sup' Finset.univ_nonempty (fun k' => B i k' + C k' j) + w j := by
            have := Finset.le_sup' (fun k' => B i k' + C k' j) (Finset.mem_univ k)
            linarith
        _ ≤ _ := Finset.le_sup' (fun j => Finset.univ.sup' Finset.univ_nonempty
              (fun k' => B i k' + C k' j) + w j) (Finset.mem_univ j)
  -- adding a constant to the vector adds it to the product
  have hshift : ∀ (B : Matrix ι ι ℝ) (c : ℝ) (w : ι → ℝ),
      tmulVec B (fun k => c + w k) = fun i => c + tmulVec B w i := by
    intro B c w
    funext i
    simp only [tmulVec]
    apply le_antisymm
    · refine Finset.sup'_le _ _ fun j _ => ?_
      have := Finset.le_sup' (fun j => B i j + w j) (Finset.mem_univ j)
      linarith
    · obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
        (fun j => B i j + w j)
      rw [hj]
      have := Finset.le_sup' (fun j => B i j + (c + w j)) (Finset.mem_univ j)
      linarith
  have hA : tmulVec A v = fun k => lam + v k := funext h
  induction m with
  | zero =>
    rw [show tpow A 0 = A from rfl, hA]
    funext i
    simp
  | succ m ih =>
    rw [show tpow A (m + 1) = tmul (tpow A m) A from rfl, hassoc, hA, hshift, ih]
    funext i
    push_cast
    ring
