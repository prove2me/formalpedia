-- Prove2me | solution 1 for BookSixth.standardizing_time_maps_are_similarities
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-27T13:22:22.460747+00:00
-- url     : https://prove2.me/submissions/5acf902c-5be1-4fa1-a12a-5c2b03f9ebc8

import Mathlib
import Definitions.Def_BookSixth
import Definitions.Def_BookSixthRotations3
import Definitions.Def_BookSixthRotTriple
import Theorems.Thm_BookSixth_affine_and_translate_families
import Theorems.Thm_BookSixth_rotTriple_isotopy
import Theorems.Thm_BookSixth_threefold_rotation_preserves_inner_product
import Theorems.Thm_BookSixth_round_frame_angles
import Theorems.Thm_BookSixth_pointwise_isotopy_wrappers
import Theorems.Thm_BookSixth_frame_rotation_aligns_u
import Theorems.Thm_BookSixth_frame_rotation_aligns_v

noncomputable section

open scoped BigOperators
open BookSixth Matrix

set_option maxHeartbeats 4000000

/-- Pythagoras in the plane: if `(c, d)` is a unit vector then
`(c * a - d * b, d * a + c * b)` has the same squared length as `(a, b)`. -/
private lemma plane_pythagoras (a b c d : ℝ) (h : c ^ 2 + d ^ 2 = 1) :
    (c * a - d * b) ^ 2 + (d * a + c * b) ^ 2 = a ^ 2 + b ^ 2 := by
  calc (c * a - d * b) ^ 2 + (d * a + c * b) ^ 2
      = (c ^ 2 + d ^ 2) * (a ^ 2 + b ^ 2) := by ring
    _ = 1 * (a ^ 2 + b ^ 2) := by rw [h]
    _ = a ^ 2 + b ^ 2 := by ring

/-- Every time map of the standardising isotopy of a single round circle is a
positive scalar composed with an inner-product-preserving linear map and a
translation.

The time map is the composite of the positive affine rescaling and the
rotation-plus-translation, so it has the pointwise form

    H t x = rotTriple t θ₁ θ₂ θ₃ (exp (-(t * log r)) • (x - t • c)) + t • a.

The linear part is `rotTriple t θ₁ θ₂ θ₃`, whose inner-product preservation is
the Proved `threefold_rotation_preserves_inner_product`, and the scalar is
positive for every real `t` because `r > 0`. -/
theorem solution (D : Set Space3) (hroundD : RoundCircle D) (k : ℕ) :
    ∃ H : ℝ → Space3 ≃ₜ Space3,
      Continuous (fun p : ℝ × Space3 => H p.1 p.2) ∧
      Continuous (fun p : ℝ × Space3 => (H p.1).symm p.2) ∧
      (∀ x, H 0 x = x) ∧
      (H 1) '' D = standardCircle k ∧
      (∀ t, ∃ A : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ), ∃ a : ℝ, ∃ b : (Fin 3 → ℝ), 0 < a ∧
        (∀ x y : (Fin 3 → ℝ), (∑ i, (A x) i * (A y) i) = ∑ i, x i * y i) ∧
        (∀ x : (Fin 3 → ℝ), H t x = a • (A x) + b)) := by
  obtain ⟨c, u, v, r, hr, hu, hv, huv, hD⟩ := hroundD
  obtain ⟨θ1, θ2, θ3, h1a, h1b, h2a, h2b, h3a, h3b, hρ2, hd0⟩ :=
    BookSixth.round_frame_angles u v hu hv huv
  -- The first two Givens rotations are genuine plane rotations, so the squared
  -- length is preserved at each stage.
  have hrot1 : (Real.sin θ1) ^ 2 + (Real.cos θ1) ^ 2 = 1 := Real.sin_sq_add_cos_sq θ1
  have hrot2 : (Real.sin θ2) ^ 2 + (Real.cos θ2) ^ 2 = 1 := Real.sin_sq_add_cos_sq θ2
  have hrot1' : (Real.cos θ1) ^ 2 + (Real.sin θ1) ^ 2 = 1 := Real.cos_sq_add_sin_sq θ1
  have hrot2' : (Real.cos θ2) ^ 2 + (Real.sin θ2) ^ 2 = 1 := Real.cos_sq_add_sin_sq θ2
  set A1 : ℝ := Real.sin θ1 * v 0 + Real.cos θ1 * v 1 with hA1def
  set P : ℝ := Real.cos θ1 * v 0 - Real.sin θ1 * v 1 with hPdef
  set A2 : ℝ := Real.sin θ2 * P + Real.cos θ2 * v 2 with hA2def
  set Q : ℝ := Real.cos θ2 * P - Real.sin θ2 * v 2 with hQdef
  -- `A1`, the third coordinate `A2` and the second coordinate of the rotated `v`
  -- exhaust the three plane rotations, so their squares sum to `‖v‖² = 1`.
  -- With the third Givens identity `hd0` zeroing that second coordinate this
  -- leaves `A1^2 + A2^2 = 1`.
  have hsq : A1 ^ 2 + A2 ^ 2 = 1 := by
    have hstage1 : P ^ 2 + A1 ^ 2 = v 0 ^ 2 + v 1 ^ 2 := by
      simpa only [hPdef, hA1def] using
        (plane_pythagoras (v 0) (v 1) (Real.cos θ1) (Real.sin θ1) hrot1')
    have hstage2 : Q ^ 2 + A2 ^ 2 = P ^ 2 + v 2 ^ 2 := by
      simpa only [hQdef, hA2def] using
        (plane_pythagoras P (v 2) (Real.cos θ2) (Real.sin θ2) hrot2')
    have hQ0 : Q = 0 := by simpa only [hQdef, hPdef] using hd0
    have hn : v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 = 1 := by
      have hn' := hv
      simp only [Fin.sum_univ_succ] at hn'
      norm_num [Fin.isValue] at hn'
      ring_nf at hn'
      exact hn'
    nlinarith
  -- The published `h3a`/`h3b` mix `u` into the `v`-terms, so they are not usable
  -- directly.  The third Givens lemma, applied to the two surviving `v`-components
  -- `(A1, A2)`, supplies exactly the magnitude-plus-sign pair that the frame
  -- alignment of `v` needs.
  obtain ⟨β, hperp, hsign⟩ := BookSixth.pointwise_isotopy_wrappers.2.2 A1 A2
  have hρ3 : Real.cos β * A1 - Real.sin β * A2 = 1 := by
    nlinarith [hsq, hperp, hsign, Real.sin_sq_add_cos_sq β]
  have hρ3' : Real.cos β * (Real.sin θ1 * v 0 + Real.cos θ1 * v 1)
      - Real.sin β * (Real.sin θ2 * (Real.cos θ1 * v 0 - Real.sin θ1 * v 1)
        + Real.cos θ2 * v 2) = 1 := by
    simpa only [hA1def, hA2def, hPdef] using hρ3
  obtain ⟨H, hH1, hH2, hH0, hHpt⟩ :=
    BookSixth.pointwise_isotopy_wrappers.2.1
      (fun t x => Real.exp (-(t * Real.log r)) • (x - t • c))
      (fun t x => rotTriple t θ1 θ2 β x + t • ![3 * (k : ℝ), 0, 0])
      (by
        obtain ⟨H, h1, h2, h0, hd⟩ := BookSixth.affine_and_translate_families.1 c r hr
        exact ⟨H, h1, h2, h0, hd⟩)
      (by
        obtain ⟨H, h1, h2, h0, hd⟩ :=
          BookSixth.rotTriple_isotopy θ1 θ2 β ![3 * (k : ℝ), 0, 0]
        exact ⟨H, h1, h2, h0, hd⟩)
  refine ⟨H, hH1, hH2, hH0, ?_, ?_⟩
  · have key : ∀ s : ℝ, H 1 (c + (r * Real.cos s) • u + (r * Real.sin s) • v)
        = ![3 * (k : ℝ) + Real.cos s, Real.sin s, 0] := by
      intro s
      have hu' := BookSixth.frame_rotation_aligns_u θ1 θ2 β u h1a h2a hρ2
      have hv' := BookSixth.frame_rotation_aligns_v θ1 θ2 β v hv hρ3' hd0
      have he : Real.exp (-(1 * Real.log r)) = r⁻¹ := by
        rw [Real.exp_neg, one_mul, Real.exp_log hr, inv_eq_one_div]
      have hinner : r⁻¹ • ((c + (r * Real.cos s) • u + (r * Real.sin s) • v) - (1 : ℝ) • c)
          = Real.cos s • u + Real.sin s • v := by
        rw [smul_sub, smul_add, smul_add, smul_smul, smul_smul, one_smul]
        calc r⁻¹ • c + (r⁻¹ * (r * Real.cos s)) • u + (r⁻¹ * (r * Real.sin s)) • v
              - r⁻¹ • c
            = (1 * Real.cos s) • u + (1 * Real.sin s) • v := by
              have h1 : r⁻¹ * r = 1 := inv_mul_cancel₀ hr.ne'
              rw [← mul_assoc, h1, ← mul_assoc, h1]
              abel
          _ = Real.cos s • u + Real.sin s • v := by rw [one_mul, one_mul]
      calc H 1 (c + (r * Real.cos s) • u + (r * Real.sin s) • v)
          = rotTriple 1 θ1 θ2 β (Real.exp (-(1 * Real.log r)) •
              ((c + (r * Real.cos s) • u + (r * Real.sin s) • v) - 1 • c))
              + 1 • ![3 * (k : ℝ), 0, 0] := hHpt _ _
        _ = rotTriple 1 θ1 θ2 β (Real.cos s • u + Real.sin s • v)
              + ![3 * (k : ℝ), 0, 0] := by
            rw [he, hinner, one_smul]
        _ = ![3 * (k : ℝ) + Real.cos s, Real.sin s, 0] := by
            rw [map_add, map_smul, map_smul, hu', hv']
            funext i
            fin_cases i <;> simp <;> ring
    unfold standardCircle
    rw [hD, ← Set.image_univ, Set.image_image, ← Set.image_univ, Set.image_congr]
    intro s _
    exact key s
  · intro t
    refine ⟨rotTriple t θ1 θ2 β, Real.exp (-(t * Real.log r)),
      Real.exp (-(t * Real.log r)) • (-(rotTriple t θ1 θ2 β (t • c)))
        + t • ![3 * (k : ℝ), 0, 0], ?_, ?_, ?_⟩
    · exact Real.exp_pos _
    · intro x y
      exact BookSixth.threefold_rotation_preserves_inner_product t θ1 θ2 β x y
    · intro x
      rw [hHpt, map_smul, map_sub, map_smul]
      module
