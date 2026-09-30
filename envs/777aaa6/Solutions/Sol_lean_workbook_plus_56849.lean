-- Prove2me | solution 1 for lean_workbook_plus_56849
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:27:56.788851+00:00
-- url     : https://prove2.me/submissions/6d05b29e-00f7-4248-9104-bf57f2307d44

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace CubicNormInfiniteTriples

def form (a b d : ℤ) : ℤ := 9 * a ^ 3 + 4 * b ^ 3 + 48 * d ^ 3 - 36 * a * b * d

def step (p : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ :=
  (9073 * p.1 + 6924 * p.2.1 + 15852 * p.2.2,
   11889 * p.1 + 9073 * p.2.1 + 20772 * p.2.2,
   5193 * p.1 + 3963 * p.2.1 + 9073 * p.2.2)

def orbit : ℕ → ℤ × ℤ × ℤ
  | 0 => (145, 190, 83)
  | n + 1 => step (orbit n)

theorem step_preserves (a b d : ℤ) :
    form (9073 * a + 6924 * b + 15852 * d)
      (11889 * a + 9073 * b + 20772 * d)
      (5193 * a + 3963 * b + 9073 * d) = form a b d := by
  dsimp [form]
  ring

theorem step_positive (a b d : ℤ) (ha : 0 < a) (hb : 0 < b) (hd : 0 < d) :
    0 < 9073 * a + 6924 * b + 15852 * d ∧
      0 < 11889 * a + 9073 * b + 20772 * d ∧
      0 < 5193 * a + 3963 * b + 9073 * d ∧
      a < 9073 * a + 6924 * b + 15852 * d := by
  omega

theorem orbit_properties (n : ℕ) :
    0 < (orbit n).1 ∧ 0 < (orbit n).2.1 ∧ 0 < (orbit n).2.2 ∧
      form (orbit n).1 (orbit n).2.1 (orbit n).2.2 = 1 := by
  induction n with
  | zero => norm_num [orbit, form]
  | succ n ih =>
      obtain ⟨ha, hb, hd, hform⟩ := ih
      have hp := step_positive (orbit n).1 (orbit n).2.1 (orbit n).2.2 ha hb hd
      exact ⟨hp.1, hp.2.1, hp.2.2.1,
        (step_preserves (orbit n).1 (orbit n).2.1 (orbit n).2.2).trans hform⟩

theorem first_strictMono : StrictMono (fun n => (orbit n).1) := by
  apply strictMono_nat_of_lt_succ
  intro n
  obtain ⟨ha, hb, hd, _⟩ := orbit_properties n
  exact (step_positive (orbit n).1 (orbit n).2.1 (orbit n).2.2 ha hb hd).2.2.2

theorem orbit_solution (n : ℕ) :
    9 * (orbit n).1 ^ 3 + 4 * (orbit n).2.1 ^ 3 - 48 * (-(orbit n).2.2) ^ 3 +
      36 * (orbit n).1 * (orbit n).2.1 * (-(orbit n).2.2) = 1 := by
  calc
    _ = form (orbit n).1 (orbit n).2.1 (orbit n).2.2 := by dsimp [form]; ring
    _ = 1 := (orbit_properties n).2.2.2

theorem infinite_solutions :
    {p : ℤ × ℤ × ℤ | 9 * p.1 ^ 3 + 4 * p.2.1 ^ 3 - 48 * p.2.2 ^ 3 +
      36 * p.1 * p.2.1 * p.2.2 = 1}.Infinite := by
  let f : ℕ → ℤ × ℤ × ℤ := fun n => ((orbit n).1, (orbit n).2.1, -(orbit n).2.2)
  have hinj : Function.Injective f := by
    intro i j hij
    apply first_strictMono.injective
    have hfirst := congrArg (fun p : ℤ × ℤ × ℤ => p.1) hij
    exact hfirst
  have hrange : (Set.range f).Infinite := Set.infinite_range_of_injective hinj
  apply hrange.mono
  rintro p ⟨n, rfl⟩
  exact orbit_solution n

end CubicNormInfiniteTriples

theorem solution : ∃ a b c : ℤ, 9 * a ^ 3 + 4 * b ^ 3 - 48 * c ^ 3 + 36 * a * b * c = 1 := by
  obtain ⟨⟨a, b, c⟩, h⟩ := CubicNormInfiniteTriples.infinite_solutions.nonempty
  exact ⟨a, b, c, h⟩
