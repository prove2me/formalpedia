-- Prove2me | solution 1 for NonDesarguesianWorlds.unique_line_through
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:34:34.462708+00:00
-- url     : https://prove2.me/submissions/6ae32b2e-f64b-4f14-b424-b94ecb29f531

-- Sol generated from Geometry/NonDesarguesianWorlds.lean
import Mathlib
import Definitions.Def_Geometry_NonDesarguesianWorlds

/-!
# Projective completion of a planar ternary ring

This file isolates the incidence-theoretic core of coordinatization.  Multiplication
need not be associative: the three solution axioms of a planar ternary operation
are exactly what the usual affine-coordinate proof needs in order to construct a
projective plane.
-/

open NonDesarguesianWorlds

















open NonDesarguesianWorlds in
theorem solution{α : Type*} (R : PlanarTernaryRing α)
    {P Q : Point α} (hne : P ≠ Q) :
    ∃! L : Line α, Incident R P L ∧ Incident R Q L := by
  rcases P with ⟨x₁, y₁⟩ | m₁ | rfl
  · rcases Q with ⟨x₂, y₂⟩ | m₂ | rfl
    · -- Both affine
      by_cases hx : x₁ = x₂
      · -- Same x-coordinate: vertical line
        subst hx
        refine ⟨Line.vertical x₁, ?_, ?_⟩
        · trivial
        · intro L hL
          rcases L with ⟨m, b⟩ | ⟨a⟩ | ⟨⟩
          · simp [Incident] at hL; cases hne (by simp_all)
          · simp [Incident] at hL; rw [hL]
          · simp [Incident] at hL
      · -- Different x-coordinates: use two_points
        have ⟨mb, ⟨hb₁, hb₂⟩, hb_unique⟩ := R.two_points hx y₁ y₂
        use Line.ordinary mb.1 mb.2
        refine ⟨⟨by simp [Incident, hb₁], by simp [Incident, hb₂]⟩, ?_⟩
        intro L hL
        rcases L with ⟨m, b'⟩ | ⟨a⟩ | ⟨_⟩
        · simp [Incident] at hL
          have heq := (hb_unique (m, b') ⟨hL.1.symm, hL.2.symm⟩).symm
          rw [heq]
        · simp [Incident] at hL; exact absurd (hL.1.trans hL.2.symm) hx
        · simp [Incident] at hL
    · -- P affine, Q ideal
      have ⟨b, hb, hb_unique⟩ := R.intercept x₁ m₂ y₁
      use Line.ordinary m₂ b
      refine ⟨⟨by simp [Incident, hb], rfl⟩, ?_⟩
      intro L hL
      rcases L with ⟨m, b'⟩ | ⟨a⟩ | ⟨⟩
      · simp [Incident] at hL
        have hm : m = m₂ := hL.2.symm
        have hb' : R.ternary x₁ m₂ b' = y₁ := by rw [← hm]; exact hL.1.symm
        rw [← hm]; simp [hb_unique b' hb']
      · simp [Incident] at hL
      · simp [Incident] at hL
    · -- P affine, Q verticalIdeal
      refine ⟨Line.vertical x₁, ?_, ?_⟩
      · trivial
      · intro L hL
        rcases L with ⟨_⟩ | ⟨_⟩ | ⟨_⟩
        · simp [Incident] at hL
        · simp [Incident] at hL; rw [hL]
        · simp [Incident] at hL
  · -- P ideal
    rcases Q with ⟨x₂, y₂⟩ | m₂ | rfl
    · -- P ideal, Q affine
      have ⟨b, hb, hb_unique⟩ := R.intercept x₂ m₁ y₂
      use Line.ordinary m₁ b
      refine ⟨⟨rfl, by simp [Incident, hb]⟩, ?_⟩
      intro L hL
      rcases L with ⟨m, b'⟩ | ⟨a⟩ | ⟨⟩
      · simp [Incident] at hL
        have hm : m = m₁ := hL.1.symm
        have hb' : R.ternary x₂ m₁ b' = y₂ := by rw [← hm]; exact hL.2.symm
        rw [← hm]; simp [hb_unique b' hb']
      · simp [Incident] at hL
      · simp [Incident] at hL
    · -- P ideal m₁, Q ideal m₂
      refine ⟨Line.atInfinity, ?_, ?_⟩
      · trivial
      · intro L hL
        rcases L with ⟨m, b⟩ | a | ⟨⟩
        · exfalso; simp [Incident] at hL; exact hne (congrArg Point.ideal (hL.1.trans hL.2.symm))
        · cases hL.1
        · trivial
    · -- P ideal, Q verticalIdeal
      refine ⟨Line.atInfinity, ?_, ?_⟩
      · trivial
      · intro L hL
        rcases L with ⟨_⟩ | ⟨_⟩ | ⟨_⟩
        · simp [Incident] at hL
        · simp [Incident] at hL
        · trivial
  · -- P verticalIdeal
    rcases Q with ⟨x₂, y₂⟩ | m₂ | rfl
    · -- P verticalIdeal, Q affine
      refine ⟨Line.vertical x₂, ?_, ?_⟩
      · trivial
      · intro L hL
        rcases L with ⟨_⟩ | ⟨_⟩ | ⟨_⟩
        · simp [Incident] at hL
        · simp [Incident] at hL; rw [hL]
        · simp [Incident] at hL
    · -- P verticalIdeal, Q ideal
      refine ⟨Line.atInfinity, ?_, ?_⟩
      · trivial
      · intro L hL
        rcases L with ⟨_⟩ | ⟨_⟩ | ⟨_⟩
        · simp [Incident] at hL
        · simp [Incident] at hL
        · trivial
    · -- P verticalIdeal, Q verticalIdeal (contradiction)
      contradiction
