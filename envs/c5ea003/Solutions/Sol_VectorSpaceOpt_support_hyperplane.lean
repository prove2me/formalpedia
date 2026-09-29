-- Prove2me | solution 1 for VectorSpaceOpt.support_hyperplane
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-26T12:47:58.397216+00:00
-- url     : https://prove2.me/submissions/a63591fc-7a3e-4812-b137-37785fdd2f7a

import Mathlib


theorem solution {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (K : Set X) (hK : Convex ℝ K) (hKi : (interior K).Nonempty)
    (x : X) (hx : x ∉ interior K) :
    ∃ f : X →L[ℝ] ℝ, f ≠ 0 ∧ ∀ k ∈ K, f k ≤ f x := by
  exact geometric_hahn_banach_of_nonempty_interior_point hK hx hKi
