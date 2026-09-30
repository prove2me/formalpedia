-- Prove2me | solution 1 for lean_workbook_plus_60997
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:37:50.697245+00:00
-- url     : https://prove2.me/submissions/fbaa5ba1-06bc-467f-8f3b-bb4f0cad8ff9

import Mathlib

noncomputable section

namespace SpherePlaneClassification

def system (R t x y z : ℝ) : Prop :=
  x ^ 2 + y ^ 2 + z ^ 2 = R ∧ x + y + 2 * z = t

def rx (t u v : ℝ) : ℝ := (t + 2 * v + 3 * u) / 6
def ry (t u v : ℝ) : ℝ := (t + 2 * v - 3 * u) / 6
def rz (t _u v : ℝ) : ℝ := (t - v) / 3

theorem norm_identity (x y z : ℝ) :
    6 * (x ^ 2 + y ^ 2 + z ^ 2) =
      (x + y + 2 * z) ^ 2 + 3 * (x - y) ^ 2 + 2 * (x + y - z) ^ 2 := by ring

theorem reconstructed_coordinates (t u v : ℝ) :
    rx t u v + ry t u v + 2 * rz t u v = t ∧
      rx t u v - ry t u v = u ∧ rx t u v + ry t u v - rz t u v = v := by
  dsimp [rx, ry, rz]
  constructor
  · ring
  constructor <;> ring

theorem reconstructed_norm (t u v : ℝ) :
    6 * ((rx t u v) ^ 2 + (ry t u v) ^ 2 + (rz t u v) ^ 2) =
      t ^ 2 + 3 * u ^ 2 + 2 * v ^ 2 := by
  dsimp [rx, ry, rz]
  ring

theorem reconstructed_system_iff (R t u v : ℝ) :
    system R t (rx t u v) (ry t u v) (rz t u v) ↔
      3 * u ^ 2 + 2 * v ^ 2 = 6 * R - t ^ 2 := by
  have hn := reconstructed_norm t u v
  constructor
  · intro h
    nlinarith only [h.1, hn]
  · intro h
    exact ⟨by nlinarith only [h, hn], (reconstructed_coordinates t u v).1⟩

theorem full_parametrization (R t x y z : ℝ) :
    system R t x y z ↔ ∃ u v : ℝ,
      3 * u ^ 2 + 2 * v ^ 2 = 6 * R - t ^ 2 ∧
        x = rx t u v ∧ y = ry t u v ∧ z = rz t u v := by
  constructor
  · rintro ⟨hn, ht⟩
    refine ⟨x - y, x + y - z, ?_, ?_, ?_, ?_⟩
    · have h := norm_identity x y z
      rw [hn, ht] at h
      linarith only [h]
    · dsimp [rx]; linarith only [ht]
    · dsimp [ry]; linarith only [ht]
    · dsimp [rz]; linarith only [ht]
  · rintro ⟨u, v, h, rfl, rfl, rfl⟩
    exact (reconstructed_system_iff R t u v).mpr h

theorem parameter_unique (t u v u' v' : ℝ)
    (hx : rx t u v = rx t u' v') (hy : ry t u v = ry t u' v')
    (hz : rz t u v = rz t u' v') : u = u' ∧ v = v' := by
  have h := reconstructed_coordinates t u v
  have h' := reconstructed_coordinates t u' v'
  rw [hx, hy, hz] at h
  exact ⟨h.2.1.symm.trans h'.2.1, h.2.2.symm.trans h'.2.2⟩

theorem necessary_bound (R t x y z : ℝ) (h : system R t x y z) : t ^ 2 ≤ 6 * R := by
  have hn := norm_identity x y z
  rw [h.1, h.2] at hn
  nlinarith only [hn, sq_nonneg (x - y), sq_nonneg (x + y - z)]

theorem existence_iff (R t : ℝ) :
    (∃ x y z : ℝ, system R t x y z) ↔ t ^ 2 ≤ 6 * R := by
  constructor
  · rintro ⟨x, y, z, h⟩
    exact necessary_bound R t x y z h
  · intro ht
    let u := Real.sqrt ((6 * R - t ^ 2) / 3)
    have hu : u ^ 2 = (6 * R - t ^ 2) / 3 :=
      Real.sq_sqrt (div_nonneg (sub_nonneg.mpr ht) (by norm_num))
    refine ⟨rx t u 0, ry t u 0, rz t u 0, ?_⟩
    apply (reconstructed_system_iff R t u 0).mpr
    nlinarith only [hu]

theorem boundary_iff (R t x y z : ℝ) (ht : t ^ 2 = 6 * R) :
    system R t x y z ↔ x = t / 6 ∧ y = t / 6 ∧ z = t / 3 := by
  constructor
  · intro h
    obtain ⟨u, v, huv, hx, hy, hz⟩ := (full_parametrization R t x y z).mp h
    have hu : u ^ 2 = 0 := by nlinarith only [huv, ht, sq_nonneg u, sq_nonneg v]
    have hv : v ^ 2 = 0 := by nlinarith only [huv, ht, sq_nonneg u, sq_nonneg v]
    have hu0 : u = 0 := eq_zero_of_pow_eq_zero hu
    have hv0 : v = 0 := eq_zero_of_pow_eq_zero hv
    simpa [hu0, hv0, rx, ry, rz] using And.intro hx (And.intro hy hz)
  · rintro ⟨rfl, rfl, rfl⟩
    constructor
    · nlinarith only [ht]
    · ring

theorem interior_two_solutions (R t : ℝ) (ht : t ^ 2 < 6 * R) :
    ∃ x y z x' y' z' : ℝ,
      system R t x y z ∧ system R t x' y' z' ∧ x ≠ x' := by
  let u := Real.sqrt ((6 * R - t ^ 2) / 3)
  have hu : u ^ 2 = (6 * R - t ^ 2) / 3 :=
    Real.sq_sqrt (div_nonneg (sub_nonneg.mpr ht.le) (by norm_num))
  have hu0 : 0 < u := Real.sqrt_pos.mpr (div_pos (sub_pos.mpr ht) (by norm_num))
  refine ⟨rx t u 0, ry t u 0, rz t u 0, rx t (-u) 0, ry t (-u) 0, rz t (-u) 0,
    ?_, ?_, ?_⟩
  · apply (reconstructed_system_iff R t u 0).mpr
    nlinarith only [hu]
  · apply (reconstructed_system_iff R t (-u) 0).mpr
    nlinarith only [hu]
  · intro h
    dsimp [rx] at h
    linarith only [h, hu0]

theorem source_infeasible (x y z : ℝ)
    (hn : x ^ 2 + y ^ 2 + z ^ 2 = 1) (ht : x + y + 2 * z = Real.sqrt 7) : False := by
  have hb := necessary_bound 1 (Real.sqrt 7) x y z ⟨hn, ht⟩
  have hs : (Real.sqrt 7) ^ 2 = 7 := Real.sq_sqrt (by norm_num)
  nlinarith only [hb, hs]

theorem boundary_sqrt_six (x y z : ℝ) :
    system 1 (Real.sqrt 6) x y z ↔
      x = Real.sqrt 6 / 6 ∧ y = Real.sqrt 6 / 6 ∧ z = Real.sqrt 6 / 3 := by
  apply boundary_iff
  norm_num [Real.sq_sqrt]

end SpherePlaneClassification

theorem solution (x y z : ℝ) (h₁ : x ^ 2 + y ^ 2 + z ^ 2 = 1)
    (h₂ : x + y + 2 * z = Real.sqrt 7) : x = 2 / 3 ∧ y = 2 / 3 ∧ z = 1 / 3 := by
  exact (SpherePlaneClassification.source_infeasible x y z h₁ h₂).elim

#print axioms SpherePlaneClassification.norm_identity
#print axioms SpherePlaneClassification.reconstructed_coordinates
#print axioms SpherePlaneClassification.reconstructed_norm
#print axioms SpherePlaneClassification.reconstructed_system_iff
#print axioms SpherePlaneClassification.full_parametrization
#print axioms SpherePlaneClassification.parameter_unique
#print axioms SpherePlaneClassification.necessary_bound
#print axioms SpherePlaneClassification.existence_iff
#print axioms SpherePlaneClassification.boundary_iff
#print axioms SpherePlaneClassification.interior_two_solutions
#print axioms SpherePlaneClassification.source_infeasible
#print axioms SpherePlaneClassification.boundary_sqrt_six
#print axioms solution
