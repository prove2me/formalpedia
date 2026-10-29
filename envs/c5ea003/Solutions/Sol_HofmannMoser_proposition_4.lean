-- Prove2me | solution 1 for HofmannMoser.proposition_4
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T22:33:25.613973+00:00
-- url     : https://prove2.me/submissions/7137dd5a-fe4d-46c6-a9e6-d1698dc1eae5

import Definitions.Def_HofmannMoser_Potential
import Mathlib

universe u

namespace HM4Aux

theorem swap_sum {α : Type*} {k : Nat} (g : α × Fin k → Nat) (l : List (α × Fin k)) :
    ∑ s : Fin k, ((l.filter (fun tr => tr.2 == s)).map g).sum = (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have h : ∀ s : Fin k, ((List.filter (fun tr => tr.2 == s) (a :: l)).map g).sum =
        (if a.2 = s then g a else 0) + ((l.filter (fun tr => tr.2 == s)).map g).sum := by
      intro s
      by_cases hs : a.2 = s <;> simp [List.filter_cons, hs]
    rw [Finset.sum_congr rfl (fun s _ => h s), Finset.sum_add_distrib, ih]
    simp

theorem foldl_mul_eq_prod {n : Nat} (g : Fin n → Nat) :
    (List.ofFn g).foldl (· * ·) 1 = ∏ i, g i := by
  rw [← List.prod_ofFn]
  rw [List.prod_eq_foldl]

end HM4Aux

open HofmannMoser in
theorem solution {C : Nat → Type u} (A : TreeAutomaton C) (v : Value C) :
    A.basic v ≤ A.stateCount ^ v.size := by
  classical
  have key : ∀ v : Value C, ∑ s : Fin A.stateCount, A.runCount v s ≤ A.stateCount ^ v.size := by
    intro v
    induction v with
    | node c vs ih =>
      rename_i n
      have hrc : ∀ s, A.runCount (Value.node c vs) s =
          (((A.rules n c).filter (fun tr ↦ tr.2 == s)).map fun (tr : (Fin n → Fin A.stateCount) × Fin A.stateCount) ↦
            ∏ i, A.runCount (vs i) (tr.1 i)).sum := by
        intro s
        rw [TreeAutomaton.runCount.eq_1 A s]
        simp only [HM4Aux.foldl_mul_eq_prod]
      simp only [hrc]
      rw [HM4Aux.swap_sum (fun (tr : (Fin n → Fin A.stateCount) × Fin A.stateCount) => ∏ i, A.runCount (vs i) (tr.1 i)) (A.rules n c)]
      rw [← List.sum_toFinset _ (A.no_duplicate_rules n c)]
      calc ∑ tr ∈ (A.rules n c).toFinset, ∏ i, A.runCount (vs i) (tr.1 i)
          ≤ ∑ tr : (Fin n → Fin A.stateCount) × Fin A.stateCount,
              ∏ i, A.runCount (vs i) (tr.1 i) :=
            Finset.sum_le_sum_of_subset (Finset.subset_univ _)
        _ = A.stateCount * ∏ i, ∑ s, A.runCount (vs i) s := by
            rw [Fintype.sum_prod_type, Fintype.prod_sum]
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
            rw [Finset.mul_sum]
        _ ≤ A.stateCount * ∏ i, A.stateCount ^ (vs i).size := by
            gcongr with i
            exact ih i
        _ = A.stateCount ^ (Value.node c vs).size := by
            rw [Finset.prod_pow_eq_pow_sum, Value.size, List.sum_ofFn, pow_add, pow_one]
  calc A.basic v = A.runCount v A.final := rfl
    _ ≤ ∑ s : Fin A.stateCount, A.runCount v s :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
    _ ≤ _ := key v

