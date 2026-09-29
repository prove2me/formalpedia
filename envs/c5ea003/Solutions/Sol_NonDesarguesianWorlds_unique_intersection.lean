-- Prove2me | solution 1 for NonDesarguesianWorlds.unique_intersection
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:34:33.96641+00:00
-- url     : https://prove2.me/submissions/2708f914-a395-49ab-9868-93fe553d142b

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
    {L K : Line α} (hne : L ≠ K) :
    ∃! P : Point α, Incident R P L ∧ Incident R P K := by
  cases L <;> cases K <;> try trivial
  -- ordinary m b, ordinary n c
  · rename_i m b n c
    by_cases h : m = n
    · -- same slope, different intercepts: meet at ideal point
      subst h
      refine ⟨Point.ideal m, ⟨rfl, rfl⟩, ?_⟩
      intro y hy
      rcases y with ⟨x, y'⟩ | ⟨m'⟩ | ⟨⟩
      · simp [Incident] at hy
        have huniq := R.intercept x m y'
        have hbc := huniq.unique hy.1.symm hy.2.symm
        exact False.elim (hne (by rw [hbc]))
      · simp [Incident] at hy; rw [hy]
      · simp [Incident] at hy
    · -- different slopes: use two_slopes
      obtain ⟨⟨x, y⟩, ⟨hx₁, hx₂⟩, huniq⟩ := R.two_slopes h b c
      use Point.affine x y
      refine ⟨⟨hx₁, hx₂⟩, ?_⟩
      intro P ⟨hPL, hPK⟩
      match P with
      | Point.affine x' y' =>
        simp [Incident] at hPL hPK
        have heq := huniq (x', y') ⟨hPL, hPK⟩
        rw [Prod.ext_iff] at heq
        exact congrArg₂ Point.affine heq.1 heq.2
      | Point.ideal m' =>
        simp [Incident] at hPL hPK
        exact False.elim (h (hPL.symm.trans hPK))
      | Point.verticalIdeal => simp [Incident] at hPL
  -- ordinary m b, vertical a
  · rename_i m b a
    use Point.affine a (R.ternary a m b)
    refine ⟨⟨rfl, rfl⟩, ?_⟩
    intro P ⟨hPL, hPK⟩
    match P with
    | Point.affine x' y' =>
      simp [Incident] at hPL hPK
      rw [hPK] at hPL
      exact congrArg₂ Point.affine hPK hPL
    | Point.ideal m' => simp [Incident] at hPK
    | Point.verticalIdeal => simp [Incident] at hPL
  -- ordinary m b, atInfinity
  · rename_i m b
    use Point.ideal m
    refine ⟨⟨rfl, trivial⟩, ?_⟩
    intro P ⟨hPL, hPK⟩
    match P with
    | Point.affine x' y' => simp [Incident] at hPK
    | Point.ideal m' => simp_all [Incident]
    | Point.verticalIdeal => simp [Incident] at hPL
  -- vertical a, ordinary m b
  · rename_i a m b
    use Point.affine a (R.ternary a m b)
    refine ⟨⟨rfl, rfl⟩, ?_⟩
    intro P ⟨hPL, hPK⟩
    match P with
    | Point.affine x' y' =>
      simp [Incident] at hPL hPK
      rw [hPL] at hPK
      exact congrArg₂ Point.affine hPL hPK
    | Point.ideal m' => simp [Incident] at hPL
    | Point.verticalIdeal => simp [Incident] at hPK
  -- vertical a, vertical b with a ≠ b
  · rename_i a b
    use Point.verticalIdeal
    refine ⟨⟨trivial, trivial⟩, ?_⟩
    intro P ⟨hPL, hPK⟩
    match P with
    | Point.affine x' y' => simp_all [Incident]
    | Point.ideal m' => simp_all [Incident]
    | Point.verticalIdeal => rfl
  -- vertical a, atInfinity
  · rename_i a
    use Point.verticalIdeal
    refine ⟨⟨trivial, trivial⟩, ?_⟩
    intro P ⟨hPL, hPK⟩
    match P with
    | Point.affine x' y' => simp_all [Incident]
    | Point.ideal m' => simp_all [Incident]
    | Point.verticalIdeal => rfl
  -- atInfinity, ordinary m b
  · rename_i m b
    use Point.ideal m
    refine ⟨⟨trivial, rfl⟩, ?_⟩
    intro P ⟨hPL, hPK⟩
    match P with
    | Point.affine x' y' => simp_all [Incident]
    | Point.ideal m' => simp_all [Incident]
    | Point.verticalIdeal => simp [Incident] at hPK
  -- atInfinity, vertical a
  · rename_i a
    use Point.verticalIdeal
    refine ⟨⟨trivial, trivial⟩, ?_⟩
    intro P ⟨hPL, hPK⟩
    match P with
    | Point.affine x' y' => simp_all [Incident]
    | Point.ideal m' => simp_all [Incident]
    | Point.verticalIdeal => rfl
