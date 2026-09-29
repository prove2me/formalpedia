-- Prove2me | solution 1 for mme_split_pair_product_mass_le
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T06:41:12.80903+00:00
-- url     : https://prove2.me/submissions/edd96b24-4160-4773-a0f2-86acf3b33bba

import Definitions.Def_mme_recursive_thin_split_data
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FinCases

open scoped BigOperators
open MME.RecursiveThinSplit

private theorem split_pair_injective {half : ℕ} {parent : Fin 3 → ℕ}
    (i j : Fin 3) (hij : i ≠ j) :
    Function.Injective (fun c : Split half parent => (c.val i, c.val j)) := by
  intro a b h
  have hi := congrArg (fun p => (p.1 : Fin (half + 1)).val) h
  have hj := congrArg (fun p => (p.2 : Fin (half + 1)).val) h
  have ha := a.property.1
  have hb := b.property.1
  apply Subtype.ext
  funext k
  apply Fin.ext
  fin_cases i <;> fin_cases j <;> fin_cases k <;> norm_num at *
  all_goals
    simp_all only [show (⟨2, by decide⟩ : Fin 3) = 2 from rfl] <;> omega

/-- Two distinct grades determine a split. Consequently, a product of two
nonnegative coordinate weights has no more mass on splits than on all pairs. -/
theorem solution {half : ℕ} {parent : Fin 3 → ℕ}
    (i j : Fin 3) (hij : i ≠ j)
    (p q : Fin (half + 1) → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hq : ∀ b, 0 ≤ q b) :
    (∑ c : Split half parent, p (c.val i) * q (c.val j)) ≤
      (∑ a, p a) * (∑ b, q b) := by
  classical
  let f := fun c : Split half parent => (c.val i, c.val j)
  have hinj : Function.Injective f := split_pair_injective i j hij
  calc
    _ = ∑ pair ∈ Finset.univ.image f, p pair.1 * q pair.2 := by
      rw [Finset.sum_image]
      exact fun a _ b _ h => hinj h
    _ ≤ ∑ pair : Fin (half + 1) × Fin (half + 1), p pair.1 * q pair.2 :=
      Finset.sum_le_univ_sum_of_nonneg (fun pair => mul_nonneg (hp _) (hq _))
    _ = _ := by rw [Fintype.sum_prod_type, Fintype.sum_mul_sum]


#print axioms solution
