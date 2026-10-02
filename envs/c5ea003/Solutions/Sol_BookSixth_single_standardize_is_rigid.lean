-- Prove2me | solution 1 for BookSixth.single_standardize_is_rigid
-- status  : ACCEPTED   (disprove)
-- author  : @WillR
-- created : 2026-09-26T02:04:10.251492+00:00
-- url     : https://prove2.me/submissions/b1bb8521-483d-40bd-9f02-7be5f65f184c

import Mathlib
import Definitions.Def_BookSixth

open scoped BigOperators
open BookSixth

/-- The circle of radius 2 centred at the origin in the plane `z = 0` is a genuine
round circle, with centre the origin, directions `![1,0,0]` and `![0,1,0]`, and
radius 2. -/
private theorem round_radius_two :
    RoundCircle (Set.range (fun t : ℝ => (2 * Real.cos t) • ![1, 0, 0]
      + (2 * Real.sin t) • ![0, 1, 0])) := by
  refine ⟨(![0, 0, 0] : Space3), (![1, 0, 0] : Space3), (![0, 1, 0] : Space3), 2, by norm_num, ?_, ?_, ?_, ?_⟩
  · simp [Fin.sum_univ_three]
  · simp [Fin.sum_univ_three]
  · simp [Fin.sum_univ_three]
  · congr 1
    funext t
    funext i
    fin_cases i <;> simp [smul_eq_mul] <;> ring

/-- Any two points of `standardCircle k` have squared separation at most 4: they share
the same first-coordinate offset `3 * k` and the same third coordinate, and the first
two coordinates each range over an interval of length 2. -/
private theorem sc_k_diam_le_four {k : ℕ} {x y : Space3}
    (hx : x ∈ standardCircle k) (hy : y ∈ standardCircle k) :
    (∑ i, (x i - y i) * (x i - y i)) ≤ 4 := by
  unfold standardCircle at hx hy
  obtain ⟨s, rfl⟩ := hx
  obtain ⟨t, rfl⟩ := hy
  have e0 : (![3 * (k : ℝ) + Real.cos s, Real.sin s, 0] : Space3) 0
      = 3 * (k : ℝ) + Real.cos s := rfl
  have e1 : (![3 * (k : ℝ) + Real.cos s, Real.sin s, 0] : Space3) 1
      = Real.sin s := rfl
  have e2 : (![3 * (k : ℝ) + Real.cos s, Real.sin s, 0] : Space3) 2 = 0 := rfl
  have f0 : (![3 * (k : ℝ) + Real.cos t, Real.sin t, 0] : Space3) 0
      = 3 * (k : ℝ) + Real.cos t := rfl
  have f1 : (![3 * (k : ℝ) + Real.cos t, Real.sin t, 0] : Space3) 1
      = Real.sin t := rfl
  have f2 : (![3 * (k : ℝ) + Real.cos t, Real.sin t, 0] : Space3) 2 = 0 := rfl
  simp only [Fin.sum_univ_three]
  rw [e0, e1, e2, f0, f1, f2]
  have hoff : (3 * (k : ℝ) + Real.cos s) - (3 * (k : ℝ) + Real.cos t)
      = Real.cos s - Real.cos t := by ring
  have hz : (0:ℝ) - (0:ℝ) = 0 := by ring
  rw [hoff, hz]
  show (Real.cos s - Real.cos t) * (Real.cos s - Real.cos t)
    + (Real.sin s - Real.sin t) * (Real.sin s - Real.sin t) + 0 * 0 ≤ 4
  have hz2 : (0:ℝ) * 0 = 0 := by ring
  rw [hz2]
  -- The chord of a unit circle: the squared chord length is `2 - 2 * cos (s - t)`.
  have hid : (Real.cos s - Real.cos t) * (Real.cos s - Real.cos t)
      + (Real.sin s - Real.sin t) * (Real.sin s - Real.sin t)
      = 2 - 2 * Real.cos (s - t) := by
    rw [Real.cos_sub]
    nlinarith [Real.cos_sq_add_sin_sq s, Real.cos_sq_add_sin_sq t]
  rw [hid]
  nlinarith [Real.neg_one_le_cos (s - t)]

/-- An orthogonal linear map preserves the squared separation `sum (x - y) * (x - y)`. -/
private theorem ortho_sep {A : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ)}
    (hA : ∀ x y : Space3, (∑ i, (A x) i * (A y) i) = ∑ i, x i * y i) (x y : Space3) :
    (∑ i, (A x - A y) i * (A x - A y) i) = (∑ i, (x - y) i * (x - y) i) := by
  have key : (A x - A y) = A (x - y) := (map_sub A x y).symm
  rw [key]
  simpa only [Pi.sub_apply] using hA (x - y) (x - y)

/-- `single_standardize_is_rigid` is false.

It asks for a motion whose every value is an unscaled Euclidean isometry followed by a
translation. An isometry preserves squared separations, so the pair of antipodal points
of `D` would have to be sent to a pair of the same squared separation inside
`standardCircle k`. Choosing `D` to be the circle of radius 2 gives a pair at squared
separation 16, whereas every pair of points of `standardCircle k` has squared
separation at most 4. So no isometry can carry that `D` onto `standardCircle k`, for any
`k`, and the statement is refuted. -/
theorem solution : ¬ (∀ (D : Set Space3) (k : ℕ) (hroundD : RoundCircle D),
    ∃ K : ℝ → Space3 ≃ₜ Space3,
      Continuous (fun p : ℝ × Space3 => K p.1 p.2) ∧
      Continuous (fun p : ℝ × Space3 => (K p.1).symm p.2) ∧
      (∀ x, K 0 x = x) ∧
      (K 1) '' D = standardCircle k ∧
      (∀ t, ∃ A : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ), ∃ q : ℝ × Space3,
        (∀ x y : Space3, (∑ i, (A x) i * (A y) i) = ∑ i, x i * y i) ∧
        (∀ x : Space3, (K t) x = (A x) + q.2))) := by
  intro h
  set D : Set Space3 := Set.range (fun t : ℝ => (2 * Real.cos t) • ![1, 0, 0]
    + (2 * Real.sin t) • ![0, 1, 0]) with hD
  obtain ⟨K, _, _, _, hK1, hpoint⟩ := h D 0 round_radius_two
  obtain ⟨A, q, hA, hmap⟩ := hpoint 1
  -- The two antipodal points of `D`, named `p` and `n`.
  -- The `Space3` ascription sits on the vector, never on the whole scalar multiple:
  -- otherwise `![1, 0, 0]` is elaborated first and defaults to `Fin 3 -> Nat`, so
  -- `(2 : ℝ) • _` demands an `HSMul ℝ (Fin 3 -> Nat)` that does not exist.
  have hp : (2 : ℝ) • (![1, 0, 0] : Space3) ∈ D := by
    rw [hD]
    refine ⟨0, ?_⟩
    funext i
    fin_cases i <;> simp [smul_eq_mul, Real.cos_zero, Real.sin_zero] <;> ring
  have hn : (-2 : ℝ) • (![1, 0, 0] : Space3) ∈ D := by
    rw [hD]
    refine ⟨Real.pi, ?_⟩
    funext i
    fin_cases i <;> simp [smul_eq_mul, Real.cos_pi, Real.sin_pi] <;> ring
  -- Their images lie in `standardCircle 0`.
  have hpx : (K 1) ((2 : ℝ) • (![1, 0, 0] : Space3)) ∈ standardCircle 0 := by
    rw [← hK1]
    exact Set.mem_image_of_mem _ hp
  have hnx : (K 1) ((-2 : ℝ) • (![1, 0, 0] : Space3)) ∈ standardCircle 0 := by
    rw [← hK1]
    exact Set.mem_image_of_mem _ hn
  -- The isometry sends the pair to a pair of the same squared separation.
  have hmap' : ∀ x, (K 1) x = A x + q.2 := hmap
  -- Stated pointwise, because the diameter bound below elaborates with `Pi.sub_apply`
  -- pushed into the summand, so the two statements must have the same shape.
  have hsep : (∑ i, (((K 1) ((2 : ℝ) • (![1, 0, 0] : Space3))) i
        - ((K 1) ((-2 : ℝ) • (![1, 0, 0] : Space3))) i)
      * (((K 1) ((2 : ℝ) • (![1, 0, 0] : Space3))) i
        - ((K 1) ((-2 : ℝ) • (![1, 0, 0] : Space3))) i)) = 16 := by
    -- The antipodal difference is the constant vector `(4 : ℝ) • ![1, 0, 0]`.
    have hd : ((2 : ℝ) • (![1, 0, 0] : Space3)) - ((-2 : ℝ) • (![1, 0, 0] : Space3))
        = (4 : ℝ) • (![1, 0, 0] : Space3) := by
      funext i
      fin_cases i <;> norm_num [Pi.smul_apply, smul_eq_mul]
    -- Push the inner difference through `A`, then replace it by `hd`.
    have hsub : ∀ i, ((K 1) ((2 : ℝ) • (![1, 0, 0] : Space3))) i
          - ((K 1) ((-2 : ℝ) • (![1, 0, 0] : Space3))) i
        = A ((2 : ℝ) • (![1, 0, 0] : Space3)) i - A ((-2 : ℝ) • (![1, 0, 0] : Space3)) i := by
      intro i
      -- `hmap'` is already pointwise, so rewrite with it and let `abel` cancel `q.2`.
      rw [hmap', hmap']
      simp only [Pi.add_apply]
      abel
    -- `hsub` is pointwise and the binder `i` is local to the `∑`, so push it in with
    -- `simp` rather than `rw`, whose pattern cannot see the bound index.
    simp only [hsub]
    have hsep' := ortho_sep hA ((2 : ℝ) • (![1, 0, 0] : Space3))
      ((-2 : ℝ) • (![1, 0, 0] : Space3))
    simp only [Pi.sub_apply] at hsep'
    -- `hsep'` reads A-side = raw-side, and the goal is the A-side, so rewrite forward.
    rw [hsep']
    have hsum : (∑ i, (((2 : ℝ) • (![1, 0, 0] : Space3))
          - ((-2 : ℝ) • (![1, 0, 0] : Space3))) i
        * (((2 : ℝ) • (![1, 0, 0] : Space3))
          - ((-2 : ℝ) • (![1, 0, 0] : Space3))) i) = 16 := by
      -- `hd` is stated on the vectors, so push it under the bound index with `simp`;
      -- then evaluate the three concrete coordinates. `<;>` applies `norm_num` to every
      -- remaining goal and is a no-op if `simp` has already closed them all.
      simp only [hd]
      simp [Fin.sum_univ_three, Pi.smul_apply, smul_eq_mul] <;> norm_num
    -- `exact` rather than `rw [hsum]`: `hsum` and the goal differ only in the bound
    -- variable name (`i` versus `x`), which `exact` treats as alpha-equivalent, while
    -- `rw` matches the binder syntactically and fails.
    exact hsum
  -- But the image pair lies in `standardCircle 0`, so its separation is at most 4.
  have hle := sc_k_diam_le_four (k := 0) hpx hnx
  rw [hsep] at hle
  linarith
