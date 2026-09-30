-- Prove2me | solution 1 for pell_equation_general
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T02:59:06.43213+00:00
-- url     : https://prove2.me/submissions/54d729af-bda2-47b2-b150-68237bc3d962

import Mathlib.NumberTheory.Pell

theorem solution (d : ℕ) (hd : ¬ ∃ k : ℕ, d = k ^ 2) :
    {(x, y) : ℤ × ℤ | x ^ 2 - d * y ^ 2 = 1}.Infinite := by
  have hdpos : 0 < d := by
    by_contra h
    have hd0 : d = 0 := by omega
    exact hd ⟨0, by simp [hd0]⟩
  have hdnonsquare : ¬ IsSquare (d : ℤ) := by
    rintro ⟨z, hz⟩
    apply hd
    refine ⟨z.natAbs, ?_⟩
    have hcast : (d : ℤ) = (z.natAbs : ℤ) ^ 2 := by
      rw [Int.natCast_natAbs, sq_abs, pow_two]
      exact hz
    exact_mod_cast hcast
  obtain ⟨a, ha⟩ := Pell.IsFundamental.exists_of_not_isSquare
    (show (0 : ℤ) < d by exact_mod_cast hdpos) hdnonsquare
  let f : ℤ → ℤ × ℤ := fun n => ((a ^ n).x, (a ^ n).y)
  have hf : Function.Injective f := by
    intro n m h
    exact ha.y_strictMono.injective (congrArg Prod.snd h)
  refine (Set.infinite_range_of_injective hf).mono ?_
  rintro p ⟨n, rfl⟩
  exact (a ^ n).prop

#print axioms solution
