-- Prove2me | solution 1 for lean_workbook_plus_57196
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:08:35.247747+00:00
-- url     : https://prove2.me/submissions/57c594b0-36ef-4d8e-a6f2-28ef6f875b0c

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Tactic

set_option autoImplicit false

namespace ComplexConicParametrization

def Equation (x y z : ℂ) : Prop := x * y + z * y = x * z

def param (r s : ℂ) : ℂ × ℂ × ℂ :=
  (r * (r + s), r * s, s * (r + s))

theorem parameter_model (r s : ℂ) :
    Equation (r * (r + s)) (r * s) (s * (r + s)) := by
  unfold Equation
  ring

theorem rank_one_identity (x y z : ℂ) :
    Equation x y z ↔ (x - y) * (z - y) = y ^ 2 := by
  unfold Equation
  constructor <;> intro h <;> linear_combination -h

theorem coordinate_recovery (r s : ℂ) :
    (param r s).1 - (param r s).2.1 = r ^ 2 ∧
    (param r s).2.2 - (param r s).2.1 = s ^ 2 := by
  unfold param
  constructor <;> ring

theorem parametrization_iff (x y z : ℂ) :
    Equation x y z ↔ ∃ r s : ℂ,
      x = r * (r + s) ∧ y = r * s ∧ z = s * (r + s) := by
  constructor
  · intro h
    obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq (x - y) (by decide : 0 < (2 : ℕ))
    by_cases hr0 : r = 0
    · rw [hr0] at hr
      have hxy : x = y := by linear_combination -hr
      have hy2 : y ^ 2 = 0 := by
        rw [hxy] at h
        unfold Equation at h
        linear_combination h
      have hy : y = 0 := sq_eq_zero_iff.mp hy2
      have hx : x = 0 := hxy.trans hy
      obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq z (by decide : 0 < (2 : ℕ))
      refine ⟨0, s, ?_, ?_, ?_⟩
      · simp [hx]
      · simp [hy]
      · linear_combination -hs
    · have hp : r * (y / r) = y := by field_simp
      have hs : (y / r) ^ 2 = z - y := by
        apply mul_left_cancel₀ (pow_ne_zero 2 hr0)
        calc
          r ^ 2 * (y / r) ^ 2 = y ^ 2 := by field_simp
          _ = (x - y) * (z - y) := (rank_one_identity x y z).mp h |>.symm
          _ = r ^ 2 * (z - y) := by rw [hr]
      refine ⟨r, y / r, ?_, hp.symm, ?_⟩
      · linear_combination -hr - hp
      · linear_combination -hs - hp
  · rintro ⟨r, s, rfl, rfl, rfl⟩
    exact parameter_model r s

theorem range_eq_conic :
    Set.range (fun p : ℂ × ℂ => param p.1 p.2) =
      {p : ℂ × ℂ × ℂ | Equation p.1 p.2.1 p.2.2} := by
  ext p
  rcases p with ⟨x, y, z⟩
  constructor
  · rintro ⟨⟨r, s⟩, h⟩
    change param r s = (x, y, z) at h
    have hx : r * (r + s) = x := congrArg Prod.fst h
    have hy : r * s = y := congrArg (fun p => p.2.1) h
    have hz : s * (r + s) = z := congrArg (fun p => p.2.2) h
    change Equation x y z
    rw [← hx, ← hy, ← hz]
    exact parameter_model r s
  · intro h
    obtain ⟨r, s, hx, hy, hz⟩ := (parametrization_iff x y z).mp h
    refine ⟨(r, s), ?_⟩
    change (r * (r + s), r * s, s * (r + s)) = (x, y, z)
    rw [hx, hy, hz]

theorem param_neg (r s : ℂ) : param (-r) (-s) = param r s := by
  unfold param
  apply Prod.ext
  · ring
  · apply Prod.ext <;> ring

theorem fiber_classification (r s u v : ℂ) :
    param r s = param u v ↔
      (r = u ∧ s = v) ∨ (r = -u ∧ s = -v) := by
  constructor
  · intro h
    have hx : r * (r + s) = u * (u + v) := congrArg Prod.fst h
    have hy : r * s = u * v := congrArg (fun p => p.2.1) h
    have hz : s * (r + s) = v * (u + v) := congrArg (fun p => p.2.2) h
    have hr2 : r ^ 2 = u ^ 2 := by linear_combination hx - hy
    have hs2 : s ^ 2 = v ^ 2 := by linear_combination hz - hy
    by_cases hu : u = 0
    · rw [hu] at hr2
      have hr : r = 0 := sq_eq_zero_iff.mp (by simpa using hr2)
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs2 with hs | hs
      · exact Or.inl ⟨hr.trans hu.symm, hs⟩
      · exact Or.inr ⟨by rw [hr, hu]; ring, hs⟩
    · rcases sq_eq_sq_iff_eq_or_eq_neg.mp hr2 with hr | hr
      · refine Or.inl ⟨hr, ?_⟩
        rw [hr] at hy
        exact mul_left_cancel₀ hu hy
      · refine Or.inr ⟨hr, ?_⟩
        rw [hr] at hy
        apply mul_left_cancel₀ hu
        linear_combination -hy
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · exact param_neg u v

theorem fiber_set (r s : ℂ) :
    {p : ℂ × ℂ | param p.1 p.2 = param r s} = {(r, s), (-r, -s)} := by
  ext p
  change (param p.1 p.2 = param r s) ↔ (p = (r, s) ∨ p = (-r, -s))
  rw [fiber_classification]
  simp only [Prod.ext_iff]

theorem zero_fiber (r s : ℂ) :
    param r s = (0, 0, 0) ↔ r = 0 ∧ s = 0 := by
  have h := fiber_classification r s 0 0
  simpa [param] using h

theorem antipodal_pair_equal_iff (r s : ℂ) :
    (r, s) = (-r, -s) ↔ r = 0 ∧ s = 0 := by
  constructor
  · intro h
    have hr : r = -r := congrArg Prod.fst h
    have hs : s = -s := congrArg Prod.snd h
    constructor
    · linear_combination (1 / 2 : ℂ) * hr
    · linear_combination (1 / 2 : ℂ) * hs
  · rintro ⟨rfl, rfl⟩
    simp

theorem nonzero_fiber_card (r s : ℂ) (h : r ≠ 0 ∨ s ≠ 0) :
    ({(r, s), (-r, -s)} : Finset (ℂ × ℂ)).card = 2 := by
  classical
  have hn : (r, s) ≠ (-r, -s) := by
    intro he
    obtain ⟨hr, hs⟩ := (antipodal_pair_equal_iff r s).mp he
    rcases h with h | h
    · exact h hr
    · exact h hs
  simp [hn]

end ComplexConicParametrization

theorem solution (x y z r s : ℂ) :
    (x = r * (r + s) ∧ y = r * s ∧ z = s * (r + s)) →
      x * y + z * y = x * z := by
  rintro ⟨rfl, rfl, rfl⟩
  exact ComplexConicParametrization.parameter_model r s

#print axioms ComplexConicParametrization.parameter_model
#print axioms ComplexConicParametrization.rank_one_identity
#print axioms ComplexConicParametrization.coordinate_recovery
#print axioms ComplexConicParametrization.parametrization_iff
#print axioms ComplexConicParametrization.range_eq_conic
#print axioms ComplexConicParametrization.param_neg
#print axioms ComplexConicParametrization.fiber_classification
#print axioms ComplexConicParametrization.fiber_set
#print axioms ComplexConicParametrization.zero_fiber
#print axioms ComplexConicParametrization.antipodal_pair_equal_iff
#print axioms ComplexConicParametrization.nonzero_fiber_card
#print axioms solution
