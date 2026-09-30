-- Prove2me | solution 1 for lean_workbook_plus_82690
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:35:03.381338+00:00
-- url     : https://prove2.me/submissions/a5295e40-43fa-437a-8d27-3954050ceaf5

import Mathlib.Analysis.Matrix.Spectrum

private theorem symmetric_nilpotent_zero {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.transpose = M)
    (hnil : ∃ k : ℕ, M^k = 0) : M = 0 := by
  by_contra hne
  have hh : M.IsHermitian := by
    simpa [Matrix.IsHermitian, Matrix.conjTranspose] using hM
  obtain ⟨v, t, ht, hv, heigen⟩ := hh.exists_eigenvector_of_ne_zero hne
  have hp : ∀ k : ℕ, (M^k).mulVec v = t^k • v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, heigen,
        smul_smul, pow_succ]
  obtain ⟨k, hk⟩ := hnil
  have hpk := hp k
  rw [hk, Matrix.zero_mulVec] at hpk
  exact (smul_ne_zero (pow_ne_zero k ht) hv) hpk.symm

theorem solution (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : M.transpose = M) (hMk : ∀ k : ℕ, M ^ k = 0) : M = 0 := by
  exact symmetric_nilpotent_zero M hM ⟨2, hMk 2⟩
