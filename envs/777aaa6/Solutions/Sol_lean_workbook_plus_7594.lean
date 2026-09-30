-- Prove2me | solution 1 for lean_workbook_plus_7594
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:26:06.486737+00:00
-- url     : https://prove2.me/submissions/3345547a-1fd9-48ae-96bb-d77f75e567a4

import Mathlib.Tactic.Ring

namespace QuadraticAdjacentProduct

theorem identity (a b n : ℤ) :
    (n ^ 2 + a * n + b) * ((n + 1) ^ 2 + a * (n + 1) + b) =
      (n ^ 2 + (a + 1) * n + b) ^ 2 +
        a * (n ^ 2 + (a + 1) * n + b) + b := by
  ring

end QuadraticAdjacentProduct

theorem solution (p : ℤ → ℤ) (a b n : ℤ)
    (hp : ∀ x : ℤ, p x = x ^ 2 + a * x + b) :
    ∃ M : ℤ, p n * p (n + 1) = p M := by
  refine ⟨n ^ 2 + (a + 1) * n + b, ?_⟩
  simp only [hp]
  exact QuadraticAdjacentProduct.identity a b n

#print axioms solution
