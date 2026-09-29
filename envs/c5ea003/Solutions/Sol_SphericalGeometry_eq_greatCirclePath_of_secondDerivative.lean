-- Prove2me | solution 1 for SphericalGeometry.eq_greatCirclePath_of_secondDerivative
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-31T14:51:03.34803+00:00
-- url     : https://prove2.me/submissions/09443cb2-7d70-4ea5-b973-4334e8f33d78

import Definitions.Def_spherical_great_circle

open SphericalGeometry

universe u

theorem solution {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (alpha : ℝ) (halpha : alpha ≠ 0) (g g' g'' : ℝ → E)
    (hg : ∀ t : ℝ, HasDerivAt g (g' t) t)
    (hg' : ∀ t : ℝ, HasDerivAt g' (g'' t) t)
    (hode : ∀ t : ℝ, g'' t = -(alpha ^ 2) • g t) :
    ∀ t : ℝ, g t = greatCirclePath (g 0) (alpha⁻¹ • g' 0) (alpha * t) := by
  set v1 : E := g 0 with hv1
  set v2 : E := alpha⁻¹ • g' 0 with hv2
  -- the candidate solution and its first two derivatives
  set p : ℝ → E := fun t => Real.cos (alpha * t) • v1 + Real.sin (alpha * t) • v2 with hpdef
  set q : ℝ → E := fun t =>
    (-(alpha * Real.sin (alpha * t))) • v1 + (alpha * Real.cos (alpha * t)) • v2 with hqdef
  have hlin : ∀ t : ℝ, HasDerivAt (fun s : ℝ => alpha * s) alpha t := by
    intro t; simpa using (hasDerivAt_id t).const_mul alpha
  have hcos : ∀ t : ℝ,
      HasDerivAt (fun s => Real.cos (alpha * s)) (-(alpha * Real.sin (alpha * t))) t := by
    intro t
    have := (Real.hasDerivAt_cos (alpha * t)).comp t (hlin t)
    simpa [mul_comm] using this
  have hsin : ∀ t : ℝ,
      HasDerivAt (fun s => Real.sin (alpha * s)) (alpha * Real.cos (alpha * t)) t := by
    intro t
    have := (Real.hasDerivAt_sin (alpha * t)).comp t (hlin t)
    simpa [mul_comm] using this
  have hp : ∀ t : ℝ, HasDerivAt p (q t) t := by
    intro t
    exact ((hcos t).smul_const v1).add ((hsin t).smul_const v2)
  have hq : ∀ t : ℝ, HasDerivAt q (-(alpha ^ 2) • p t) t := by
    intro t
    have h1 : HasDerivAt (fun s => -(alpha * Real.sin (alpha * s)))
        (-(alpha * (alpha * Real.cos (alpha * t)))) t := ((hsin t).const_mul alpha).neg
    have h2 : HasDerivAt (fun s => alpha * Real.cos (alpha * s))
        (alpha * -(alpha * Real.sin (alpha * t))) t := (hcos t).const_mul alpha
    have := (h1.smul_const v1).add (h2.smul_const v2)
    convert this using 1
    rw [hpdef]
    simp only [smul_add, smul_smul]
    congr 1 <;> · congr 1; ring
  -- the difference solves the same equation with vanishing data at zero
  set f : ℝ → E := fun t => g t - p t with hfdef
  set f' : ℝ → E := fun t => g' t - q t with hf'def
  have hf : ∀ t : ℝ, HasDerivAt f (f' t) t := fun t => (hg t).sub (hp t)
  have hf' : ∀ t : ℝ, HasDerivAt f' (-(alpha ^ 2) • f t) t := by
    intro t
    have := (hg' t).sub (hq t)
    rw [hode t] at this
    convert this using 1
    rw [hfdef]
    simp only [smul_sub]
  have hf0 : f 0 = 0 := by rw [hfdef, hpdef]; simp [hv1]
  have hf'0 : f' 0 = 0 := by
    rw [hf'def, hqdef]
    simp only [mul_zero, Real.sin_zero, Real.cos_zero, mul_one, neg_zero, zero_smul, zero_add]
    rw [hv2, smul_smul, mul_inv_cancel₀ halpha, one_smul, sub_self]
  -- the conserved energy
  have hasq : (alpha : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 halpha
  have hPhi : ∀ t : ℝ, HasDerivAt
      (fun s => (inner ℝ (f s) (f s) : ℝ) + (alpha ^ 2)⁻¹ * (inner ℝ (f' s) (f' s) : ℝ)) 0 t := by
    intro t
    have d1 : HasDerivAt (fun s => (inner ℝ (f s) (f s) : ℝ))
        ((inner ℝ (f t) (f' t) : ℝ) + (inner ℝ (f' t) (f t) : ℝ)) t := (hf t).inner ℝ (hf t)
    have d2 : HasDerivAt (fun s => (inner ℝ (f' s) (f' s) : ℝ))
        ((inner ℝ (f' t) (-(alpha ^ 2) • f t) : ℝ)
          + (inner ℝ (-(alpha ^ 2) • f t) (f' t) : ℝ)) t := (hf' t).inner ℝ (hf' t)
    have hsum := d1.add (d2.const_mul (alpha ^ 2)⁻¹)
    convert hsum using 1
    simp only [inner_smul_left, inner_smul_right, RCLike.star_def, conj_trivial]
    rw [real_inner_comm (f t) (f' t)]
    field_simp
    ring
  have hconst : ∀ t : ℝ,
      (inner ℝ (f t) (f t) : ℝ) + (alpha ^ 2)⁻¹ * (inner ℝ (f' t) (f' t) : ℝ)
        = (inner ℝ (f 0) (f 0) : ℝ) + (alpha ^ 2)⁻¹ * (inner ℝ (f' 0) (f' 0) : ℝ) := by
    intro t
    exact is_const_of_deriv_eq_zero (fun s => (hPhi s).differentiableAt)
      (fun s => (hPhi s).deriv) t 0
  intro t
  have ht := hconst t
  rw [hf0, hf'0] at ht
  simp only [inner_zero_left, mul_zero, add_zero] at ht
  have hnn2 : (0:ℝ) ≤ (alpha ^ 2)⁻¹ * (inner ℝ (f' t) (f' t) : ℝ) := by
    have hpos : (0:ℝ) ≤ (alpha ^ 2)⁻¹ := by positivity
    exact mul_nonneg hpos real_inner_self_nonneg
  have hnn1 : (0:ℝ) ≤ (inner ℝ (f t) (f t) : ℝ) := real_inner_self_nonneg
  have hzero : (inner ℝ (f t) (f t) : ℝ) = 0 := by linarith
  have hft : f t = 0 := inner_self_eq_zero.mp hzero
  have hgp : g t - p t = 0 := hft
  have : g t = p t := sub_eq_zero.mp hgp
  rw [this, hpdef, greatCirclePath]
