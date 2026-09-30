-- Prove2me | solution 1 for erdos_szekeres_conjecture
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T03:31:05.383159+00:00
-- url     : https://prove2.me/submissions/6b481fad-75a2-4f45-9958-2ddbc1e64b7a

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

private def trianglePoints (i : Fin 3) : ℝ × ℝ :=
  (if i.val = 0 then 0 else 1, if i.val = 2 then 1 else 0)

private theorem triangle_injective : Function.Injective trianglePoints := by
  intro i j h
  fin_cases i <;> fin_cases j <;> norm_num [trianglePoints] at *

private theorem triangle_general :
    ∀ i j m : Fin 3, i ≠ j → j ≠ m → i ≠ m →
      ¬ ∃ t : ℝ, 0 < t ∧ t < 1 ∧
        trianglePoints m =
          ((trianglePoints i).1 + t * ((trianglePoints j).1 - (trianglePoints i).1),
           (trianglePoints i).2 + t * ((trianglePoints j).2 - (trianglePoints i).2)) := by
  intro i j m hij hjm him h
  obtain ⟨t, ht0, ht1, heq⟩ := h
  have hx := congrArg Prod.fst heq
  have hy := congrArg Prod.snd heq
  fin_cases i <;> fin_cases j <;> fin_cases m <;>
    norm_num [trianglePoints] at * <;> linarith

theorem solution : ¬ (∀ (k : ℕ), 3 ≤ k →
    ∃ (N : ℕ) (_ : N = 2 ^ (k - 2) + 1),
      ∀ (pts : Fin N → ℝ × ℝ),
        Function.Injective pts →
        (∀ i j m : Fin N, i ≠ j → j ≠ m → i ≠ m →
          ¬ ∃ t : ℝ, 0 < t ∧ t < 1 ∧
            pts m = ((pts i).1 + t * ((pts j).1 - (pts i).1),
                     (pts i).2 + t * ((pts j).2 - (pts i).2))) →
        ∃ (S : Finset (Fin N)) (_ : S.card = k),
          ∀ i ∈ S, ∀ j ∈ S, ∀ m ∈ S,
            i ≠ j → j ≠ m → i ≠ m →
            ¬ ∃ t : ℝ, 0 < t ∧ t < 1 ∧
              pts m = ((pts i).1 + t * ((pts j).1 - (pts i).1),
                       (pts i).2 + t * ((pts j).2 - (pts i).2)) → False) := by
  intro h
  obtain ⟨N, hN, hpoints⟩ := h 3 (by decide)
  norm_num at hN
  subst N
  obtain ⟨S, hS, hwrong⟩ := hpoints trianglePoints triangle_injective triangle_general
  have hSuniv : S = Finset.univ := Finset.eq_univ_of_card S (by simpa using hS)
  subst S
  apply hwrong 0 (Finset.mem_univ _) 1 (Finset.mem_univ _) 2 (Finset.mem_univ _)
    (by decide) (by decide) (by decide)
  exact ⟨0, fun ht => (lt_irrefl (0 : ℝ)) ht.1⟩
