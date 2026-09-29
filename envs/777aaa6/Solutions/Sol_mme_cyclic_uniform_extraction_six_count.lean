-- Prove2me | solution 1 for mme_cyclic_uniform_extraction_six_count
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T05:23:27.099021+00:00
-- url     : https://prove2.me/submissions/2637c5fb-e920-43b3-bf0f-6744eb26f543

import Theorems.Thm_mme_finite_MM_extraction_swap_double
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open MME
universe u

/-- Doubling a cyclic extraction squares both its copy lower bound and its
common matrix volume, and gives an extraction from the full symmetrization. -/
theorem solution
    {K : Type u} [Field K] {T : TensorObj K 3} {k V : ℕ}
    (a b c : Fin k → ℕ) (hk : 0 < k)
    (hrestrict : TensorObj.Restrict
      (TensorObj.bigAdd (fun j => MMObj K (a j) (b j) (c j))) (cyclicSymmetrization T))
    (hvolume : ∀ j, a j * b j * c j = V)
    (B : ℝ) (hB : 0 ≤ B) (hcount : B ≤ (k : ℝ)) :
    ∃ (copies : ℕ) (a' b' c' : Fin copies → ℕ),
      0 < copies ∧
      TensorObj.Restrict
        (TensorObj.bigAdd (fun j => MMObj K (a' j) (b' j) (c' j))) (sixSymmetrization T) ∧
      B ^ 2 ≤ (copies : ℝ) ∧
      ∀ j, a' j * b' j * c' j = V ^ 2 := by
  let a' := fun r : Fin (k * k) => a (finProdFinEquiv.symm r).1 * c (finProdFinEquiv.symm r).2
  let b' := fun r : Fin (k * k) => b (finProdFinEquiv.symm r).1 * b (finProdFinEquiv.symm r).2
  let c' := fun r : Fin (k * k) => c (finProdFinEquiv.symm r).1 * a (finProdFinEquiv.symm r).2
  refine ⟨k * k, a', b', c', Nat.mul_pos hk hk,
    mme_finite_MM_extraction_swap_double a b c hrestrict, ?_, ?_⟩
  · simpa only [Nat.cast_mul, pow_two] using mul_self_le_mul_self hB hcount
  · intro j
    dsimp only [a', b', c']
    calc
      _ = (a (finProdFinEquiv.symm j).1 * b (finProdFinEquiv.symm j).1 *
            c (finProdFinEquiv.symm j).1) *
          (a (finProdFinEquiv.symm j).2 * b (finProdFinEquiv.symm j).2 *
            c (finProdFinEquiv.symm j).2) := by ring
      _ = V ^ 2 := by rw [hvolume, hvolume]; ring


#print axioms solution
