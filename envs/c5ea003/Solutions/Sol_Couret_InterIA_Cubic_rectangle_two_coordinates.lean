-- Prove2me | solution 1 for Couret.InterIA.Cubic.rectangle_two_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:58:53.534654+00:00
-- url     : https://prove2.me/submissions/8df9f9cb-6762-47b4-9f9f-7bf1313b3264

import Definitions.Def_Couret_RectangleProbes_c3e716b02120
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false
namespace Couret.InterIA.Cubic



theorem scalar_rectangle_injective (h a b : ℝ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) (hneg : a ≠ -b) :
    Function.Injective (fun p : Bool × Bool => h + (if p.1 then a else 0) +
      (if p.2 then b else 0)) := by
  rintro ⟨p,q⟩ ⟨r,s⟩ he
  cases p <;> cases q <;> cases r <;> cases s <;>
    simp only [Bool.false_eq_true, ↓reduceIte, add_zero] at he <;>
    first | rfl | (exfalso; apply ha; linarith) | (exfalso; apply hb; linarith) |
      (exfalso; apply hab; linarith) | (exfalso; apply hneg; linarith)

theorem p2m_local_rectangle_two_coordinates {ι : Type*} (H U V : ι → ℝ)
    (hinj : Function.Injective (rectangle H U V)) :
    ∃ z w : ι, Function.Injective
      (fun p : Bool × Bool => (rectangle H U V p z, rectangle H U V p w)) := by
  classical
  have hU : ∃ z, U z ≠ 0 := by
    by_contra! h
    have he : rectangle H U V (true,false) = rectangle H U V (false,false) := by
      funext z
      simp [rectangle,h z]
    have hh := hinj he
    cases hh
  obtain ⟨z,hz⟩ := hU
  by_cases hv : V z = 0
  · have hV : ∃ w, V w ≠ 0 := by
      by_contra! h
      have he : rectangle H U V (false,true) = rectangle H U V (false,false) := by
        funext w
        simp [rectangle,h w]
      have hh := hinj he
      cases hh
    obtain ⟨w,hw⟩ := hV
    refine ⟨z,w,?_⟩
    rintro ⟨p,q⟩ ⟨r,s⟩ he
    have h1 := congrArg Prod.fst he
    have h2 := congrArg Prod.snd he
    cases p <;> cases q <;> cases r <;> cases s <;>
      simp only [rectangle, Bool.false_eq_true, ↓reduceIte, add_zero] at h1 h2 <;>
      first | rfl | (exfalso; apply hz; linarith) | (exfalso; apply hw; linarith)
  · by_cases heq : U z = V z
    · have hUV : ∃ w, U w ≠ V w := by
        by_contra! h
        have he : rectangle H U V (true,false) = rectangle H U V (false,true) := by
          funext w
          simp [rectangle,h w]
        have hh := hinj he
        cases hh
      obtain ⟨w,hw⟩ := hUV
      refine ⟨z,w,?_⟩
      rintro ⟨p,q⟩ ⟨r,s⟩ he
      have h1 := congrArg Prod.fst he
      have h2 := congrArg Prod.snd he
      cases p <;> cases q <;> cases r <;> cases s <;>
        simp only [rectangle, Bool.false_eq_true, ↓reduceIte, add_zero] at h1 h2 <;>
      first | rfl | (exfalso; apply hz; linarith) | (exfalso; apply hw; linarith)
    · by_cases hneg : U z = -V z
      · have hUV : ∃ w, U w + V w ≠ 0 := by
          by_contra! h
          have he : rectangle H U V (true,true) = rectangle H U V (false,false) := by
            funext w
            simp only [rectangle, Bool.false_eq_true, ↓reduceIte, add_zero]
            linarith [h w]
          have hh := hinj he
          cases hh
        obtain ⟨w,hw⟩ := hUV
        refine ⟨z,w,?_⟩
        rintro ⟨p,q⟩ ⟨r,s⟩ he
        have h1 := congrArg Prod.fst he
        have h2 := congrArg Prod.snd he
        cases p <;> cases q <;> cases r <;> cases s <;>
          simp only [rectangle, Bool.false_eq_true, ↓reduceIte, add_zero] at h1 h2 <;>
      first | rfl | (exfalso; apply hz; linarith) | (exfalso; apply hw; linarith)
      · refine ⟨z,z,?_⟩
        intro p q he
        apply scalar_rectangle_injective (H z) (U z) (V z) hz hv heq hneg
        exact congrArg Prod.fst he

end Couret.InterIA.Cubic

universe p2m_u_0
theorem solution : ∀ {ι : Type p2m_u_0} (H U V : ι → Real),
  @Function.Injective.{1, p2m_u_0 + 1} (Prod.{0, 0} Bool Bool) (ι → Real)
      (@Couret.InterIA.Cubic.rectangle.{p2m_u_0} ι H U V) →
    @Exists.{p2m_u_0 + 1} ι fun z =>
      @Exists.{p2m_u_0 + 1} ι fun w =>
        @Function.Injective.{1, 1} (Prod.{0, 0} Bool Bool) (Prod.{0, 0} Real Real) fun p =>
          @Prod.mk.{0, 0} Real Real (@Couret.InterIA.Cubic.rectangle.{p2m_u_0} ι H U V p z)
            (@Couret.InterIA.Cubic.rectangle.{p2m_u_0} ι H U V p w) := @_root_.Couret.InterIA.Cubic.p2m_local_rectangle_two_coordinates

