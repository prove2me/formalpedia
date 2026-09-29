-- Prove2me | solution 1 for lean_workbook_plus_55463
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:54:58.426378+00:00
-- url     : https://prove2.me/submissions/1bfbb0a3-12ff-4e0f-9ea8-aafc584e3c56

import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (n : ℕ) (hn : 0 < n) (A : Matrix (Fin n) (Fin n) ℤ) (hA : A.diag = 1 ∧ ∀ i j, i ≠ j → A i j = 0) : ∃ k : ℕ, A ^ k = 1 := by
  have hId : A = 1 := by
    ext i j
    by_cases hij : i=j
    · subst j
      simpa [Matrix.diag] using congrFun hA.1 i
    · simp [Matrix.one_apply, hij, hA.2 i j hij]
  refine ⟨1, ?_⟩
  simpa using hId
