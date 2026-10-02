-- Prove2me | solution 1 for BookSixth.orthonormal_frame_cross_unit_euclidean
-- status  : ACCEPTED   (disprove)
-- author  : @WillR
-- created : 2026-09-28T07:39:08.779677+00:00
-- url     : https://prove2.me/submissions/79791266-89ec-4008-9aa4-8282881976d4

import Mathlib
import Definitions.Def_BookSixth
import Mathlib.LinearAlgebra.CrossProduct

open scoped BigOperators
open BookSixth
open Matrix

/-- **`orthonormal_frame_cross_unit_euclidean` is false as stated.**

The vector `w` is an ordinary *hypothesis* binder, not an existential. The
statement therefore asserts that *every* vector `w` satisfying the three metric
conditions is *equal* to `u ⨯₃ v`. That cannot hold: `u ⨯₃ v` is only one of the
unit normals to the plane spanned by `u` and `v`.

Take `u = e₀ = ![1,0,0]`, `v = e₁ = ![0,1,0]` and `w = e₀`. Then `u`, `v` and
`w` are all unit vectors and `u` is orthogonal to `v`, so the first three
hypotheses hold, and the first two conjuncts hold as well. But the third
conjunct `(∑ i, w i * u i) = 0` reads `1 = 0`, since `w = u`.

The intended statement is the existential one, already proved as
`BookSixth.orthonormal_frame_has_unit_cross_normal` (02c1fe73): there the vector
is *chosen* to be `u ⨯₃ v` rather than universally quantified. -/
theorem solution : ¬ (∀ (u v w : Space3), (∑ i, u i * u i) = 1 →
    (∑ i, v i * v i) = 1 → (∑ i, u i * v i) = 0 →
    w = u ⨯₃ v ∧ (∑ i, w i * w i) = 1 ∧ (∑ i, w i * u i) = 0 ∧
      (∑ i, w i * v i) = 0) := by
  intro h
  -- Instantiate at `u = v₁ = w = e₀`. The three hypotheses are `1 = 0` sums
  -- over `Fin 3`, which `Fin.sum_univ_succ` turns into three explicit terms.
  have hbad := h (u := ![1, 0, 0]) (v := ![0, 1, 0]) (w := ![1, 0, 0])
    (by simp [Fin.sum_univ_succ]) (by simp [Fin.sum_univ_succ])
    (by simp [Fin.sum_univ_succ])
  -- The second conjunct says `w` is a unit vector and the third says `w ⟂ u`,
  -- but here `w = u = e₀`, so the same sum is forced to be both `1` and `0`.
  have hone : (∑ i, (![1, 0, 0] : Space3) i * (![1, 0, 0] : Space3) i) = 1 := hbad.2.1
  have hzero : (∑ i, (![1, 0, 0] : Space3) i * (![1, 0, 0] : Space3) i) = 0 := hbad.2.2.1
  exact absurd (hone.symm.trans hzero) one_ne_zero
