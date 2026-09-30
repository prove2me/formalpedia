-- Prove2me | solution 1 for lean_workbook_plus_15684
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:55:42.904709+00:00
-- url     : https://prove2.me/submissions/58e8dd47-ffb9-4e9f-8bad-1e58c0cb27a1

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

namespace PositiveCubicNormSolutions

def form (x y z : ℤ) : ℤ := x ^ 3 + 3 * y ^ 3 + 9 * z ^ 3 - 9 * x * y * z

def step (p : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ :=
  (4 * p.1 + 6 * p.2.1 + 9 * p.2.2,
   3 * p.1 + 4 * p.2.1 + 6 * p.2.2,
   2 * p.1 + 3 * p.2.1 + 4 * p.2.2)

def orbit : ℕ → ℤ × ℤ × ℤ
  | 0 => (4, 3, 2)
  | n + 1 => step (orbit n)

theorem step_preserves (x y z : ℤ) :
    form (4 * x + 6 * y + 9 * z) (3 * x + 4 * y + 6 * z)
      (2 * x + 3 * y + 4 * z) = form x y z := by
  dsimp [form]
  ring

theorem step_growth (x y z : ℤ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    x < 4 * x + 6 * y + 9 * z ∧
      y < 3 * x + 4 * y + 6 * z ∧ z < 2 * x + 3 * y + 4 * z := by
  omega

theorem orbit_properties (n : ℕ) :
    0 < (orbit n).1 ∧ 0 < (orbit n).2.1 ∧ 0 < (orbit n).2.2 ∧
      form (orbit n).1 (orbit n).2.1 (orbit n).2.2 = 1 := by
  induction n with
  | zero => norm_num [orbit, form]
  | succ n ih =>
      obtain ⟨hx, hy, hz, hform⟩ := ih
      have hg := step_growth (orbit n).1 (orbit n).2.1 (orbit n).2.2 hx hy hz
      exact ⟨lt_trans hx hg.1, lt_trans hy hg.2.1, lt_trans hz hg.2.2,
        (step_preserves (orbit n).1 (orbit n).2.1 (orbit n).2.2).trans hform⟩

theorem coordinates_strictMono :
    StrictMono (fun n => (orbit n).1) ∧
      StrictMono (fun n => (orbit n).2.1) ∧ StrictMono (fun n => (orbit n).2.2) := by
  have hg (n : ℕ) := step_growth (orbit n).1 (orbit n).2.1 (orbit n).2.2
    (orbit_properties n).1 (orbit_properties n).2.1 (orbit_properties n).2.2.1
  exact ⟨strictMono_nat_of_lt_succ (fun n => (hg n).1),
    strictMono_nat_of_lt_succ (fun n => (hg n).2.1),
    strictMono_nat_of_lt_succ (fun n => (hg n).2.2)⟩

theorem coordinate_lower_bounds (n : ℕ) :
    (n : ℤ) + 1 ≤ (orbit n).1 ∧ (n : ℤ) + 1 ≤ (orbit n).2.1 ∧
      (n : ℤ) + 1 ≤ (orbit n).2.2 := by
  induction n with
  | zero => norm_num [orbit]
  | succ n ih =>
      obtain ⟨hx, hy, hz, _⟩ := orbit_properties n
      have hg := step_growth (orbit n).1 (orbit n).2.1 (orbit n).2.2 hx hy hz
      simp only [orbit, step, Nat.cast_add, Nat.cast_one]
      omega

theorem simultaneous_cofinality (B : ℤ) :
    ∃ x y z : ℤ, 0 < x ∧ 0 < y ∧ 0 < z ∧ form x y z = 1 ∧
      B < x ∧ B < y ∧ B < z := by
  have hp := orbit_properties B.natAbs
  have hl := coordinate_lower_bounds B.natAbs
  have hB : B ≤ (B.natAbs : ℤ) := Int.le_natAbs
  refine ⟨(orbit B.natAbs).1, (orbit B.natAbs).2.1, (orbit B.natAbs).2.2,
    hp.1, hp.2.1, hp.2.2.1, hp.2.2.2, ?_⟩
  omega

theorem infinite_positive_solutions :
    {p : ℤ × ℤ × ℤ | 0 < p.1 ∧ 0 < p.2.1 ∧ 0 < p.2.2 ∧
      p.1 ^ 3 + 3 * p.2.1 ^ 3 + 9 * p.2.2 ^ 3 - 9 * p.1 * p.2.1 * p.2.2 = 1}.Infinite := by
  have hinj : Function.Injective orbit := by
    intro i j hij
    apply coordinates_strictMono.1.injective
    exact congrArg (fun p : ℤ × ℤ × ℤ => p.1) hij
  have hrange : (Set.range orbit).Infinite := Set.infinite_range_of_injective hinj
  apply hrange.mono
  rintro p ⟨n, rfl⟩
  exact orbit_properties n

theorem infinite_integer_solutions :
    {p : ℤ × ℤ × ℤ | p.1 ^ 3 + 3 * p.2.1 ^ 3 + 9 * p.2.2 ^ 3 -
      9 * p.1 * p.2.1 * p.2.2 = 1}.Infinite := by
  apply infinite_positive_solutions.mono
  intro p hp
  exact hp.2.2.2

end PositiveCubicNormSolutions

theorem solution : ∃ c : ℤ, ∀ d : ℤ, ∃ x y z : ℤ,
    x ^ 3 + 3 * y ^ 3 + 9 * z ^ 3 - 9 * x * y * z = 1 ∧
      x > c ∧ y > c ∧ z > c := by
  refine ⟨0, ?_⟩
  intro d
  obtain ⟨x, y, z, hx, hy, hz, hform, _⟩ :=
    PositiveCubicNormSolutions.simultaneous_cofinality (max 0 d)
  exact ⟨x, y, z, hform, hx, hy, hz⟩
