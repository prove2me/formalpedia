-- Prove2me | solution 1 for mme_released_interior_child_scale_identities
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T05:29:40.22657+00:00
-- url     : https://prove2.me/submissions/3ca73829-46f2-4f57-9962-02667bef00b9

import Definitions.Def_mme_released_interior_integer_profiles
import Mathlib.Tactic.Ring

open MME MME.RecursiveYZ MME.ReleasedInterior MME.MoreAsymmetryExactSeed MME.CompleteSplit

/-- The denominator-multiple extraction scale gives exactly the physical
child position count and every scaled integer marginal, including empty cells. -/
theorem solution
    (owner : Fin 6) (s : Fin 45) (r : Fin 6) (c : Split s) (k : ℕ) :
    let scale := (seed owner s).region.getD r.val 0 *
      (splitWeight owner s r c +
        splitWeight owner s r (complement (parent_total s r) c)) * denominator
    2 * (denominator * (k * scale)) =
      (2 * k) * (splitCount owner s r c +
        splitCount owner s r (complement (parent_total s r) c)) ∧
    ∀ (i : Fin 3) (w : CompleteWord 2),
      2 * (k * scale) * childMarginal owner s r c i w =
        (2 * k) * integerProfile owner s i ⟨r, c⟩ w := by
  dsimp only
  constructor
  · unfold splitCount
    ring
  · intro i w
    unfold integerProfile
    ring


#print axioms solution
