-- Prove2me | solution 1 for mme_recursive_yz_count_full_cell
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T10:25:29.585822+00:00
-- url     : https://prove2.me/submissions/828f8cf2-536d-4bd4-bff4-4343ab608a63

import Definitions.Def_mme_recursive_yz_physical_words
import Theorems.Thm_mme_recursive_yz_count_sigma_fiber

open MME.RecursiveYZ

/-- Counting a full recursive cell reduces to its two-half position block. -/
theorem solution
    {half R : ℕ} {parent : Fin R → Fin 3 → ℕ} {n : Fin R → ℕ}
    {W : Type*} (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (a : Address half R parent n) (f : Position n → W)
    (r : Fin R) (c : MME.RecursiveThinSplit.Split half (parent r)) (w : W) :
    count (fullCell htotal a) f ⟨r,c⟩ w =
      count (fun t : Fin (n r) × Fin 2 =>
        if t.2 = 0 then a r t.1 else complement (htotal r) (a r t.1))
        (fun t => f ⟨r,t⟩) c w := by
  exact mme_recursive_yz_count_sigma_fiber
    (fun r (t : Fin (n r) × Fin 2) =>
      if t.2 = 0 then a r t.1 else complement (htotal r) (a r t.1)) f r c w


#print axioms solution
