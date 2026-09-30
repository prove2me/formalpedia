-- Prove2me | solution 1 for lean_workbook_plus_6917
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T22:36:52.119813+00:00
-- url     : https://prove2.me/submissions/66ee3a97-2dea-4b19-8825-90636e49a9be

import Mathlib

set_option autoImplicit false

noncomputable section

namespace ReciprocalForcingClassification

def Equation (h f : Real -> Real) : Prop :=
  forall x, f x + x * f (1 / x) = h x

def Compatible (h : Real -> Real) : Prop :=
  forall x, x ≠ 0 -> h x = x * h (1 / x)

def parametrization (h g : Real -> Real) (x : Real) : Real :=
  if x = 0 then h 0 else (h x + g x - x * g (1 / x)) / 2

theorem value_zero (h f : Real -> Real) (hf : Equation h f) : f 0 = h 0 := by
  simpa using hf 0

theorem compatibility (h f : Real -> Real) (hf : Equation h f) : Compatible h := by
  intro x hx
  have hi := hf (1 / x)
  simp only [one_div_one_div] at hi
  calc
    h x = f x + x * f (1 / x) := (hf x).symm
    _ = x * (f (1 / x) + (1 / x) * f x) := by field_simp; ring
    _ = x * h (1 / x) := congrArg (x * ·) hi

theorem parametrization_equation (h g : Real -> Real) (hh : Compatible h) :
    Equation h (parametrization h g) := by
  intro x
  by_cases hx : x = 0
  · simp [parametrization, hx]
  have hi : 1 / x ≠ 0 := one_div_ne_zero hx
  simp only [parametrization, hx, hi, if_false, one_div_one_div]
  calc
    (h x + g x - x * g (1 / x)) / 2 +
        x * ((h (1 / x) + g (1 / x) - (1 / x) * g x) / 2) =
        (h x + x * h (1 / x)) / 2 := by field_simp; ring
    _ = h x := by rw [<- hh x hx]; ring

theorem reconstruction (h f : Real -> Real) (hf : Equation h f) :
    f = parametrization h f := by
  funext x
  by_cases hx : x = 0
  · simpa [parametrization, hx] using value_zero h f hf
  simp only [parametrization, hx, if_false]
  rw [<- hf x]
  ring

theorem classification (h f : Real -> Real) :
    Equation h f <-> Compatible h ∧ exists g, f = parametrization h g := by
  constructor
  · intro hf
    exact ⟨compatibility h f hf, f, reconstruction h f hf⟩
  · rintro ⟨hh, g, rfl⟩
    exact parametrization_equation h g hh

theorem solvable_iff (h : Real -> Real) :
    (exists f, Equation h f) <-> Compatible h := by
  constructor
  · rintro ⟨f, hf⟩
    exact compatibility h f hf
  · intro hh
    exact ⟨parametrization h (fun _ => 0), parametrization_equation h _ hh⟩

theorem value_one (h f : Real -> Real) (hf : Equation h f) : f 1 = h 1 / 2 := by
  have hi := hf 1
  norm_num at hi
  apply (eq_div_iff (by norm_num : (2 : Real) ≠ 0)).2
  calc
    f 1 * 2 = f 1 + f 1 := by ring
    _ = h 1 := hi

theorem forcing_neg_one (h : Real -> Real) (hh : Compatible h) : h (-1) = 0 := by
  have hi := hh (-1) (by norm_num)
  norm_num at hi
  linarith

theorem homogeneous_classification (f : Real -> Real) :
    Equation (fun _ => 0) f <->
      exists g : Real -> Real, f = fun x => if x = 0 then 0 else (g x - x * g (1 / x)) / 2 := by
  have hh : Compatible (fun _ : Real => 0) := by intro x hx; simp
  constructor
  · intro hf
    obtain ⟨_, g, hg⟩ := (classification _ f).1 hf
    refine ⟨g, hg.trans ?_⟩
    funext x
    simp [parametrization]
  · rintro ⟨g, rfl⟩
    convert parametrization_equation (fun _ => 0) g hh using 1
    funext x
    simp [parametrization]

theorem constant_compatible (f : Real -> Real) (c : Real)
    (hf : forall x, 0 < x -> f x + x * f (1 / x) = c) : c = 0 := by
  have h2 := hf 2 (by norm_num)
  have hi := hf (1 / 2) (by norm_num)
  norm_num at h2 hi
  have hc : c = 2 * c := by
    calc
      c = f 2 + 2 * f (1 / 2) := h2.symm
      _ = 2 * (f (1 / 2) + (1 / 2) * f 2) := by ring
      _ = 2 * c := congrArg (2 * ·) hi
  linarith

theorem constant_solvable_iff (c : Real) :
    (exists f, Equation (fun _ => c) f) <-> c = 0 := by
  constructor
  · rintro ⟨f, hf⟩
    exact constant_compatible f c (fun x _ => hf x)
  · rintro rfl
    exact ⟨fun _ => 0, fun x => by simp⟩

theorem source_no_solution :
    ¬ (exists f : Real -> Real, forall x, 0 < x -> f x + x * f (1 / x) = 1) := by
  rintro ⟨f, hf⟩
  have hc := constant_compatible f 1 hf
  norm_num at hc

end ReciprocalForcingClassification

theorem solution (f : ℝ → ℝ) (hf : ∀ x, f x + x * f (1/x) = 1) : ∀ x, f x = 1 - x + x^2 - x^3 + x^4 - x^5 + x^6 - x^7 + x^8 - x^9 + x^10 - x^11 + x^12 - x^13 + x^14 - x^15 + x^16 - x^17 + x^18 - x^19 + x^20 - x^21 + x^22 - x^23 + x^24 - x^25 + x^26 - x^27 + x^28 - x^29 + x^30 - x^31 + x^32 - x^33 + x^34 - x^35 + x^36 - x^37 + x^38 - x^39 + x^40 - x^41 + x^42 - x^43 + x^44 - x^45 + x^46 - x^47 + x^48 - x^49 + x^50 - x^51 + x^52 - x^53 + x^54 - x^55 + x^56 - x^57 + x^58 - x^59 + x^60 - x^61 + x^62 - x^63 + x^64 - x^65 + x^66 - x^67 + x^68 - x^69 + x^70 - x^71 + x^72 - x^73 + x^74 - x^75 + x^76 - x^77 + x^78 - x^79 + x^80 - x^81 + x^82 - x^83 + x^84 - x^85 + x^86 - x^87 + x^88 - x^89 + x^90 - x^91 + x^92 - x^93 + x^94 - x^95 + x^96 - x^97 + x^98 - x^99 + x^100   :=  by
  have hc := ReciprocalForcingClassification.constant_compatible f 1
    (fun x hx => hf x)
  norm_num at hc
