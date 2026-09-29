-- Prove2me | solution 1 for mme_released_interior_112_canonical_probability
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T05:21:00.118287+00:00
-- url     : https://prove2.me/submissions/7b0484d8-815d-4080-82fc-9314230a212f

import Theorems.Thm_mme_released_interior_child_parameter_bound
import Theorems.Thm_mme_released_interior_112_child_marginal_exact
import Definitions.Def_mme_complete_split_112_address_words

open MME MME.ReleasedInterior MME.MoreAsymmetryExactSeed MME.CompleteSplit

private theorem normalized_112_marginal (p : ℕ) (hp : p ≤ denominator / 2)
    (i : Fin 3) (w : CompleteWord 2) :
    ((if i = 2 then
        if w = ![0, 2] ∨ w = ![2, 0] then p
        else if w = ![1, 1] then denominator - 2 * p else 0
      else if w = ![0, 1] ∨ w = ![1, 0] then denominator / 2 else 0 : ℕ) : ℚ) /
        denominator = CompleteSplit112.profileProbability ((p : ℚ) / denominator) i w := by
  have hsub : ((denominator - 2 * p : ℕ) : ℚ) / denominator =
      1 - 2 * ((p : ℚ) / denominator) := by
    rw [Nat.cast_sub (by norm_num [denominator] at hp ⊢; omega)]
    norm_num [denominator]
    ring
  have hword (a b : Fin 3) : w = ![a, b] ↔ w 0 = a ∧ w 1 = b := by
    simp [funext_iff, Fin.forall_fin_two]
  simp only [CompleteSplit112.profileProbability, hword, Fin.ext_iff]
  split_ifs <;> simp_all [denominator] <;> norm_num <;> tauto

/-- Swapping the high coordinate into the canonical third mode identifies
all released 112 child marginals with the canonical rational profile. -/
theorem solution
    (owner : Fin 6) (s : Fin 45) (r : Fin 6) (c : Split s) (z : Fin 3)
    (hshape : ∀ i : Fin 3, (c.val i).val = if i = z then 2 else 1) :
    let p := (((seed owner s).children.find?
      (fun a => a.1 == r.val && a.2.1 == sourceShape owner c)).getD (0, [], 0)).2.2
    ∀ (i : Fin 3) (w : CompleteWord 2),
      (childMarginal owner s r c (Equiv.swap z 2 i) w : ℚ) / denominator =
        CompleteSplit112.profileProbability ((p : ℚ) / denominator) i w := by
  dsimp only
  intro i w
  rw [mme_released_interior_112_child_marginal_exact owner s r c z hshape]
  have heq : Equiv.swap z 2 i = z ↔ i = 2 := by
    simpa only [Equiv.swap_apply_right] using
      ((Equiv.swap z 2).injective.eq_iff (a := i) (b := 2))
  simp only [heq]
  exact normalized_112_marginal _
    (mme_released_interior_child_parameter_bound owner s r (sourceShape owner c)) i w


#print axioms solution
