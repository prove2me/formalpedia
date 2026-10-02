-- Prove2me | solution 1 for BookSixth.roundness_compose_two_general
-- status  : ACCEPTED   (disprove)
-- author  : @WillR
-- created : 2026-09-26T19:15:49.045225+00:00
-- url     : https://prove2.me/submissions/be2fd90f-f7a4-4569-b880-15aff0a90c65

import Mathlib
import Definitions.Def_BookSixth

open scoped BigOperators
open BookSixth

noncomputable section

-- The unit circle in the plane spanned by `e` and `w`: centre the origin, directions `e`
-- and `w`, radius `1`. One lemma serves both planes used below, which differ only in
-- whether `e` is the `x₀`- or the `x₁`-axis vector, so the side conditions are proved once.
theorem unit_circle (e w : Space3)
    (he : (∑ i, e i * e i) = 1) (hw : (∑ i, w i * w i) = 1) (hew : (∑ i, e i * w i) = 0) :
    RoundCircle (Set.range (fun t : ℝ => (Real.cos t) • e + (Real.sin t) • w)) := by
  refine ⟨(![0,0,0] : Space3), e, w, 1, by norm_num, he, hw, hew, ?_⟩
  -- The goal is `Set.range f = Set.range g` for two pointwise-equal functions; making them
  -- syntactically equal first turns it into `rfl`. This avoids `Set.ext`, whose two branches
  -- each left a `Matrix.vecHead`/`vecTail` goal that `fin_cases` cannot index through, and
  -- `Set.range_congr`, which does not exist at this revision.
  -- Both range bodies are the same value but not the same term: the left carries the
  -- explicit centre `![0,0,0]` and radius `1 *`. So the goal is closed by rewriting the
  -- left body into the right one *as a function*, never by `rfl` and never by applying the
  -- `![…]` literal at an index (which is what produced `Matrix.vecHead`/`vecTail` goals in
  -- candidates 3540, 3542, 3544 and 3546; `Matrix.cons_val_two` is no help, since it
  -- rewrites *to* `vecHead (vecTail u)`).
  have hz : ![0,0,0] = (0 : Space3) := by
    funext i
    fin_cases i <;> simp
  have hf : (fun t : ℝ => ![0,0,0] + (1 * Real.cos t) • e + (1 * Real.sin t) • w)
      = fun t : ℝ => Real.cos t • e + Real.sin t • w := by
    funext t
    rw [hz, zero_add, one_mul, one_mul]
  rw [hf]

private abbrev G0 : Space3 ≃ₜ Space3 :=
  { toFun := fun v : Space3 => ![v 0, 2 * v 1, v 2]
    invFun := fun v : Space3 => ![v 0, v 1 / 2, v 2]
    left_inv := by intro v; funext i; fin_cases i <;> simp <;> ring
    right_inv := by intro v; funext i; fin_cases i <;> simp <;> ring }

/-- `(x₀, x₁, x₂) ↦ (x₁, x₀, x₂)`: sends the plane `x₁ = 0` to `x₀ = 0`. -/
private abbrev L0 : Space3 ≃ₜ Space3 :=
  { toFun := fun v : Space3 => ![v 1, v 0, v 2]
    invFun := fun v : Space3 => ![v 1, v 0, v 2]
    left_inv := by intro v; funext i; fin_cases i <;> simp <;> ring
    right_inv := by intro v; funext i; fin_cases i <;> simp <;> ring }

/-- The image of the unit circle of the plane `x₁ = 0` under a coordinate map that
permutes and rescales coordinates is the range of the correspondingly transformed
parametrisation, whenever the map sends each `C`-point to the `F`-point with the same
parameter. -/
lemma image_eq_range (C : Set Space3) (φ : Space3 → Space3) (F : ℝ → Space3)
    (hφ : ∀ s : ℝ, φ ((Real.cos s) • (![1,0,0] : Space3) + (Real.sin s) • (![0,0,1] : Space3))
        = F s) (hC : C = Set.range fun s : ℝ => (Real.cos s) • (![1,0,0] : Space3)
        + (Real.sin s) • (![0,0,1] : Space3)) :
    φ '' C = Set.range F := by
  refine Set.ext fun x => ?_
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [hC] at hy
    obtain ⟨s, rfl⟩ := hy
    exact ⟨s, (hφ s).symm⟩
  · rintro ⟨s, rfl⟩
    rw [hC]
    exact ⟨(Real.cos s) • (![1,0,0] : Space3) + (Real.sin s) • (![0,0,1] : Space3), ⟨s, rfl⟩, hφ s⟩

/-- **THE INVARIANT.**  If `c u v r` witness `RoundCircle E` — so `|u| = |v| = 1`,
`⟨u, v⟩ = 0`, and `E = range (fun y => c + (r * cos y) • u + (r * sin y) • v)` — then
**every point of `E` is at squared distance `r * r` from `c`.**

This single fact is the whole disproof. `hCeq` is used only to *produce* the witness `y`
inside the helper, so the existential never reaches the main proof. Every step below is a
deterministic rewrite: the cross term is *kept*, never dropped — dropping it would be
unsound, and it is `huv` that legitimately annihilates it. -/
lemma round_sphere (E : Set Space3) (c u v : Space3) (r : ℝ)
    (hu : (∑ i, u i * u i) = 1) (hv : (∑ i, v i * v i) = 1) (huv : (∑ i, u i * v i) = 0)
    (hCeq : E = Set.range (fun y : ℝ => c + (r * Real.cos y) • u + (r * Real.sin y) • v))
    (w : Space3) (hw : w ∈ E) :
    (∑ i, (w - c) i * (w - c) i) = r * r := by
  obtain ⟨y, hw⟩ := Set.mem_range.mp (hCeq ▸ hw)
  subst hw
  have key : c + (r * Real.cos y) • u + (r * Real.sin y) • v - c
      = (r * Real.cos y) • u + (r * Real.sin y) • v := by
    simp only [Pi.add_apply, Pi.smul_apply, add_assoc, add_left_comm, add_comm]
    ring
  -- `Fin.sum_univ_three` expands the goal and the three unit equations into explicit
  -- three-coordinate polynomials; no `Finset` rewriting is used.
  rw [Fin.sum_univ_three] at hu hv huv
  rw [key, Fin.sum_univ_three]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hu hv huv ⊢
  -- The identity is stated and closed once, explicitly, instead of being left to
  -- `nlinarith`'s search: the three-coordinate expansion of `‖w − c‖²` equals
  -- `r * r * (cos y * cos y + sin y * sin y)`, which is `r * r` by the Pythagorean identity.
  calc (r * Real.cos y * u 0 + r * Real.sin y * v 0)
          * (r * Real.cos y * u 0 + r * Real.sin y * v 0)
        + (r * Real.cos y * u 1 + r * Real.sin y * v 1)
          * (r * Real.cos y * u 1 + r * Real.sin y * v 1)
        + (r * Real.cos y * u 2 + r * Real.sin y * v 2)
          * (r * Real.cos y * u 2 + r * Real.sin y * v 2)
      = r * Real.cos y * (r * Real.cos y) * (u 0 * u 0 + u 1 * u 1 + u 2 * u 2)
        + r * Real.sin y * (r * Real.sin y) * (v 0 * v 0 + v 1 * v 1 + v 2 * v 2)
        + 2 * (r * Real.cos y) * (r * Real.sin y)
            * (u 0 * v 0 + u 1 * v 1 + u 2 * v 2) := by ring
    _ = r * r * (Real.cos y * Real.cos y + Real.sin y * Real.sin y) := by
        rw [hu, hv, huv]; ring
    _ = r * r := by
      -- `Real.sin_sq_add_cos_sq` is stated as `sin x ^ 2 + cos x ^ 2 = 1`, so the goal is
      -- normalised to `^ 2` form, regrouped so the common factor `r ^ 2` sits outside the
      -- sum, and the two summands swapped. `mul_one` then closes. No search tactic.
      ring_nf
      rw [← mul_add, add_comm, Real.sin_sq_add_cos_sq, mul_one]

theorem solution : ¬ (∀ {C : Set Space3} (G : ℝ → Space3 ≃ₜ Space3),
    (∀ t, RoundCircle ((G t) '' C)) → (L : ℝ → Space3 ≃ₜ Space3) →
    (∀ t, RoundCircle ((L t) '' C)) →
    ∀ t, RoundCircle ((fun s => G t (L t s)) '' C)) := by
  intro h
  -- `C` is the unit circle in the plane `x₁ = 0`; `G` and `L` are the constant families
  -- `G0` and `L0`. Applying the assumed statement to these data forces the ellipse
  -- `t ↦ (0, 2 * cos t, sin t)` to be round, which `round_sphere` refutes: its points at
  -- `s = 0` and `s = π / 2` are at squared distance `4` and `1` from any common centre.
  set fC : ℝ → Space3 := fun s : ℝ => (Real.cos s) • (![1,0,0] : Space3) + (Real.sin s) • (![0,0,1] : Space3)
  set C := Set.range fC with hC
  have hGround : ∀ t : ℝ, RoundCircle ((fun _ : ℝ => G0) t '' C) := by
    intro t
    have hset : (fun _ : ℝ => G0) t '' C = C := by
      rw [image_eq_range C G0 fC
        (by intro s; funext i; fin_cases i <;> simp [fC, smul_eq_mul] <;> ring) hC, hC]
    rw [hset]
    simpa [hC, fC] using unit_circle (![1,0,0] : Space3) (![0,0,1] : Space3) (by simp [Fin.sum_univ_three]) (by simp [Fin.sum_univ_three]) (by simp [Fin.sum_univ_three])
  have hLround : ∀ t : ℝ, RoundCircle ((fun _ : ℝ => L0) t '' C) := by
    intro t
    have himg : (fun _ : ℝ => L0) t '' C
        = Set.range (fun s : ℝ => (Real.cos s) • (![0,1,0] : Space3) + (Real.sin s) • (![0,0,1] : Space3)) :=
      image_eq_range C L0 _ (by intro s; funext i; fin_cases i <;> simp [smul_eq_mul] <;> ring) hC
    rw [himg]
    simpa [hC] using unit_circle (![0,1,0] : Space3) (![0,0,1] : Space3) (by simp [Fin.sum_univ_three]) (by simp [Fin.sum_univ_three]) (by simp [Fin.sum_univ_three])
  have hconc := h (C := C) (fun _ : ℝ => G0) hGround (fun _ : ℝ => L0) hLround 0
  -- The composite image is the ellipse `(0, 2 * cos s, sin s)`.
  have hellip : (fun s : Space3 => G0 (L0 s)) '' C
      = Set.range (fun s : ℝ => (2 * Real.cos s) • (![0,1,0] : Space3) + (Real.sin s) • (![0,0,1] : Space3)) :=
    image_eq_range C (fun v => G0 (L0 v)) _
      (by intro s; funext i; fin_cases i <;> simp [smul_eq_mul] <;> ring) hC
  rw [hellip] at hconc
  obtain ⟨c, u, v, r, hr, hu, hv, huv, hCeq⟩ := hconc
  -- **The contradiction.** `round_sphere` says every point of a round range is at the *same*
  -- squared distance `r * r` from the centre `c`. Applied at the four cardinal points of the
  -- ellipse it yields four equalities; cancelling the `‖c‖²` term in each leaves three linear
  -- equations in `c 0, c 1, c 2` which are mutually inconsistent. Membership is supplied
  -- directly by each point's own parameter, so no existential is ever introduced.
  -- The four points are `(2,0,0)`, `(0,0,1)`, `(-2,0,0)`, `(0,0,-1)`.
  have hpt : ∀ s : ℝ, (2 * Real.cos s) • (![0,1,0] : Space3)
      + (Real.sin s) • (![0,0,1] : Space3)
      ∈ Set.range (fun t : ℝ => (2 * Real.cos t) • (![0,1,0] : Space3)
        + (Real.sin t) • (![0,0,1] : Space3)) := fun s => ⟨s, rfl⟩
  have hd := round_sphere _ c u v r hu hv huv hCeq _ (hpt 0)
  have hd9 := round_sphere _ c u v r hu hv huv hCeq _ (hpt (Real.pi / 2))
  have hdp := round_sphere _ c u v r hu hv huv hCeq _ (hpt Real.pi)
  have hd27 := round_sphere _ c u v r hu hv huv hCeq _ (hpt (3 * Real.pi / 2))
  norm_num [Fin.sum_univ_three, Real.cos_zero, Real.sin_zero, Real.cos_pi_div_two,
    Real.sin_pi_div_two, Real.cos_pi, Real.sin_pi, Pi.smul_apply, Pi.sub_apply,
    Pi.add_apply, smul_eq_mul] at hd hd9 hdp hd27
  norm_num [show (3 * Real.pi / 2 : ℝ) = Real.pi + Real.pi / 2 by ring,
    Real.cos_add_pi_div_two, Real.sin_add_pi_div_two] at hd27
  -- Each conclusion is a sum of three squares equal to `r * r`, with the *same* `c 0 ^ 2`
  -- and `r * r` terms.  Subtracting cancels them, leaving three *linear* relations in
  -- `c 1` and `c 2`.  Note which coordinate each one constrains: all four cardinal points
  -- have first coordinate `0`, so `c 0` cancels out of every difference and never appears.
  -- Writing `d = (2 - c 1)^2 - c 1^2` and `e = (-c 2)^2 - (-1 - c 2)^2`, the differences
  -- expand to
  --     hd  - hdp  = -d - e            = -8 * c 1,
  --     hd9 - hd27 = e - d + 4 * c 1  = -4 * c 2,
  --     hd  - hd9  = d + e - 4 * c 1  =  3 + 2 * c 2 - 4 * c 1.
  -- The first two force `c 1 = c 2 = 0`, and the third then reads `0 = 3`.  The `3` is the
  -- axis-extent mismatch: the locus reaches `2` along the `x₁` axis but only `1` along the
  -- `x₂` axis, so no single centre can make all four equidistant.
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at hd hd9 hdp hd27
  have e1 : 8 * c 1 = 0 := by nlinarith [hd, hdp]
  have e2 : 4 * c 2 = 0 := by nlinarith [hd9, hd27]
  have e3 : 4 * c 1 - 2 * c 2 = 3 := by nlinarith [hd, hd9]
  linarith

end
