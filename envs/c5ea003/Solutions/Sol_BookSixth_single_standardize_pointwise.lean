-- Prove2me | solution 1 for BookSixth.single_standardize_pointwise
-- status  : ACCEPTED   (disprove)
-- author  : @WillR
-- created : 2026-09-25T23:59:47.924833+00:00
-- url     : https://prove2.me/submissions/89f40421-2a00-4c62-9b30-2e748ea4fea5

-- A COMPLETE, sorry-free Lean 4 disproof of the conclusion of
-- `BookSixth.single_standardize_pointwise` (89f85f15-4388-47ea-8e29-4b570e94efe9).
--
-- The target claims: for every round circle D and every k there is a motion K with
--   (K 1) '' D = standardCircle k
-- and, for every t, a witness q with
--   ∀ x, (K t) x = (q.1 • x) + q.2        -- a UNIFORM positive scaling plus a translation
--
-- Take the round circle
--   D = Set.range (fun t : ℝ => ![Real.cos t, 0, Real.sin t])
-- i.e. the unit circle in the (x, z) plane.  It is a `RoundCircle` with
--   c = ![0,0,0], u = ![1,0,0], v = ![0,0,1], r = 1.
--
-- KEY OBSERVATION.  If `∀ x, (K t) x = q.1 • x + q.2`, then at `t = 1` the image
-- `(K 1) '' D` is contained in the affine plane `{ x | x 1 = q.2 1 }`, because
-- `Pi.smul_apply` gives `(q.1 • x + q.2) 1 = q.1 * x 1 + q.2 1` and `D` has
-- identically zero second coordinate.  But `standardCircle k` is NOT contained in
-- any such plane for any `q.2`, because its second coordinate is `Real.sin t`, which
-- is not constant.  Hence `(K 1) '' D = standardCircle k` is impossible.
--
-- The refutation does not need `0 < q.1`; it fails for every real `q.1`.
-- It also does not need the time-0 or continuity conditions.
-- It does NOT contradict the accepted `BookSixth.round_circle_single_standardize`:
-- there `K 1` is the frame rotation M with rows u, v, u x v, which is an arbitrary
-- orthogonal map, not a uniform scaling.  Verified numerically: M maps the
-- (x,z)-circle exactly onto standardCircle 0.

import Mathlib
import Definitions.Def_BookSixth

open scoped BigOperators
open BookSixth

namespace BookSixth

/-- The unit circle in the (x, z) plane is a round circle. -/
theorem roundCircle_xz : RoundCircle (Set.range (fun t : ℝ => ![Real.cos t, 0, Real.sin t])) := by
  refine ⟨![0, 0, 0], ![1, 0, 0], ![0, 0, 1], 1, by norm_num, ?_, ?_, ?_, ?_⟩
  · simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
    ring
  · simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
    ring
  · simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
    ring
  · apply Set.ext
    intro y
    constructor
    · rintro ⟨t, rfl⟩
      refine ⟨t, ?_⟩
      funext i
      fin_cases i <;> simp <;> ring
    · rintro ⟨t, rfl⟩
      refine ⟨t, ?_⟩
      funext i
      fin_cases i <;> simp <;> ring

/-- If a map has the form `fun x => q.1 • x + q.2`, its image of `D` lies in the plane
`{ x | x 1 = q.2 1 }`. -/
theorem image_subset_plane (K : Space3 → Space3) (q : ℝ × Space3)
    (hK : ∀ x : Space3, K x = (q.1 • x) + q.2) :
    ∀ y ∈ K '' (Set.range (fun t : ℝ => ![Real.cos t, 0, Real.sin t])),
      y 1 = q.2 1 := by
  rintro y ⟨x, ⟨t, rfl⟩, rfl⟩
  have hstep : ((q.1 • (![Real.cos t, 0, Real.sin t] : Space3)) + q.2) 1 = q.2 1 := by
    simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hK]
  exact hstep

/-- The second coordinate of `standardCircle k` is attained with the value `0`. -/
theorem std_second_zero (k : ℕ) :
    ((fun t : ℝ => ![3 * (k : ℝ) + Real.cos t, Real.sin t, 0]) 0) 1 = 0 := by
  show Real.sin 0 = 0
  norm_num [Real.sin_zero]

/-- The second coordinate of `standardCircle k` is attained with the value `1`. -/
theorem std_second_one (k : ℕ) :
    ((fun t : ℝ => ![3 * (k : ℝ) + Real.cos t, Real.sin t, 0]) (Real.pi / 2)) 1 = 1 := by
  show Real.sin (Real.pi / 2) = 1
  norm_num [Real.sin_pi]

/-- **`standardCircle k` is not contained in any plane `{ x | x 1 = b }`. -/
theorem not_subset_plane (k : ℕ) (b : Space3) :
    ¬ (Set.range (fun t : ℝ => ![3 * (k : ℝ) + Real.cos t, Real.sin t, 0])) ⊆
        { y : Space3 | y 1 = b 1 } := by
  intro hsub
  have h0in :
      (fun t : ℝ => ![3 * (k : ℝ) + Real.cos t, Real.sin t, 0]) 0 ∈
        Set.range (fun t : ℝ => ![3 * (k : ℝ) + Real.cos t, Real.sin t, 0]) :=
    Set.mem_range_self 0
  have h1in :
      (fun t : ℝ => ![3 * (k : ℝ) + Real.cos t, Real.sin t, 0]) (Real.pi / 2) ∈
        Set.range (fun t : ℝ => ![3 * (k : ℝ) + Real.cos t, Real.sin t, 0]) :=
    Set.mem_range_self (Real.pi / 2)
  have e0 : b 1 = 0 := by
    have hmem := hsub h0in
    have heq : ((fun t : ℝ => ![3 * (k : ℝ) + Real.cos t, Real.sin t, 0]) 0) 1 = b 1 := by
      simpa only [Set.mem_setOf_eq] using hmem
    rw [std_second_zero k] at heq
    exact heq.symm
  have e1 : b 1 = 1 := by
    have hmem := hsub h1in
    have heq : ((fun t : ℝ => ![3 * (k : ℝ) + Real.cos t, Real.sin t, 0]) (Real.pi / 2)) 1
        = b 1 := by
      simpa only [Set.mem_setOf_eq] using hmem
    rw [std_second_one k] at heq
    exact heq.symm
  rw [e0] at e1
  exact absurd e1 (by norm_num)

/-- The image of the (x, z) circle under a map of the form `q.1 • x + q.2` is never
`standardCircle k`. -/
theorem image_ne_standard (K : Space3 → Space3) (q : ℝ × Space3) (k : ℕ)
    (hK : ∀ x : Space3, K x = (q.1 • x) + q.2) :
    K '' (Set.range (fun t : ℝ => ![Real.cos t, 0, Real.sin t])) ≠ standardCircle k := by
  intro hEq
  have hEq' : K '' (Set.range (fun t : ℝ => ![Real.cos t, 0, Real.sin t]))
      = Set.range (fun t : ℝ => ![3 * (k : ℝ) + Real.cos t, Real.sin t, 0]) := by
    simpa only [standardCircle] using hEq
  have hsub : (Set.range (fun t : ℝ => ![3 * (k : ℝ) + Real.cos t, Real.sin t, 0]))
      ⊆ { y : Space3 | y 1 = q.2 1 } := by
    rw [← hEq']
    exact image_subset_plane K q hK
  exact not_subset_plane k q.2 hsub

end BookSixth

open BookSixth

/-- Disproof of the target statement. The uniform-scalar form is impossible. -/
theorem solution : ¬ (∀ (D : Set Space3) (k : ℕ), RoundCircle D →
    ∃ K : ℝ → Space3 ≃ₜ Space3,
      Continuous (fun p : ℝ × Space3 => K p.1 p.2) ∧
      Continuous (fun p : ℝ × Space3 => (K p.1).symm p.2) ∧
      (∀ x, K 0 x = x) ∧
      (K 1) '' D = standardCircle k ∧
      (∀ t, ∃ q : ℝ × Space3, 0 < q.1 ∧
        (∀ x : Space3, (K t) x = (q.1 • x) + q.2))) := by
  intro hall
  obtain ⟨K, hK1, hK2, hK0, hKimg, hKpt⟩ :=
    hall (Set.range (fun t : ℝ => ![Real.cos t, 0, Real.sin t])) 0
      (BookSixth.roundCircle_xz)
  obtain ⟨q, _, hmap⟩ := hKpt 1
  exact BookSixth.image_ne_standard (K 1) q 0 hmap hKimg
