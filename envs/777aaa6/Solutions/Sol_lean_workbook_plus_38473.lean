-- Prove2me | solution 1 for lean_workbook_plus_38473
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:12:28.766529+00:00
-- url     : https://prove2.me/submissions/21b83f93-d700-42e1-bc00-2b9e06e4edbc

import Mathlib.Analysis.Complex.Basic
import Mathlib.NumberTheory.Pell
import Mathlib.Tactic

set_option autoImplicit false

lemma infinitely_many_pell_pairs (d : ℕ) (hnonsquare : ¬ ∃ k : ℕ, k ^ 2 = d)
    (hpos : 0 < d) : {p : ℤ × ℤ | p.1 ^ 2 - (d : ℤ) * p.2 ^ 2 = 1}.Infinite := by
  have hd : ¬ IsSquare (d : ℤ) := by
    rintro ⟨z, hz⟩
    apply hnonsquare
    refine ⟨z.natAbs, ?_⟩
    have habs := congrArg Int.natAbs hz
    simpa [pow_two, Int.natAbs_mul] using habs.symm
  obtain ⟨a, ha⟩ := Pell.IsFundamental.exists_of_not_isSquare
    (show (0 : ℤ) < d by exact_mod_cast hpos) hd
  have hinj : Function.Injective (fun n : ℤ => ((a ^ n).x, (a ^ n).y)) := by
    intro m n h
    exact ha.y_strictMono.injective (congrArg Prod.snd h)
  apply (Set.infinite_range_of_injective hinj).mono
  rintro p ⟨n, rfl⟩
  exact (a ^ n).prop

theorem solution (d : ℕ) (h₁ : ¬ ∃ k : ℕ, k ^ 2 = d) (h₂ : 0 < d) :
    ∃ n : ℕ, ∃ x y : ℤ, x ^ 2 - d * y ^ 2 = 1 := by
  obtain ⟨p, hp⟩ := (infinitely_many_pell_pairs d h₁ h₂).nonempty
  exact ⟨0, p.1, p.2, hp⟩

#print axioms solution
