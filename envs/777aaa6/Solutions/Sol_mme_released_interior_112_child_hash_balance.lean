-- Prove2me | solution 1 for mme_released_interior_112_child_hash_balance
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T04:53:54.896575+00:00
-- url     : https://prove2.me/submissions/28c32318-d426-45ea-84aa-79acc852ec0a

import Definitions.Def_mme_released_interior_integer_profiles
open MME MME.ReleasedInterior MME.MoreAsymmetryExactSeed

private theorem released_112_balance : ∀ (owner : Fin 6) (s : Fin 45),
    ((seed owner s).children.all (fun a =>
      if a.2.1 == [1, 1, 2] || a.2.1 == [1, 2, 1] || a.2.1 == [2, 1, 1]
      then decide (341 * (2 * a.2.2) < 100 * (denominator - 2 * a.2.2))
      else true)) = true := by
  decide +kernel

/-- Every released 112 parameter satisfies the strict balance inequality
used by the primary-hash extraction. Missing parameters are zero. -/
theorem solution
    (owner : Fin 6) (s : Fin 45) (r : Fin 6) (shape : List ℕ)
    (hshape : shape = [1, 1, 2] ∨ shape = [1, 2, 1] ∨ shape = [2, 1, 1]) :
    let p := (((seed owner s).children.find?
      (fun a => a.1 == r.val && a.2.1 == shape)).getD (0, [], 0)).2.2
    341 * (2 * p) < 100 * (denominator - 2 * p) := by
  dsimp only
  cases h : (seed owner s).children.find?
      (fun a => a.1 == r.val && a.2.1 == shape) with
  | none => norm_num [denominator]
  | some a =>
    have ha := List.mem_of_find?_eq_some h
    have heq : a.2.1 = shape := by
      have ht : a.1 = r.val ∧ a.2.1 = shape := by
        simpa using List.find?_some h
      exact ht.2
    have hs : (shape == [1, 1, 2] || shape == [1, 2, 1] ||
        shape == [2, 1, 1]) = true := by
      rcases hshape with rfl | rfl | rfl <;> decide
    have hb := List.all_eq_true.mp (released_112_balance owner s) a ha
    simpa only [heq, hs, if_true, decide_eq_true_eq, Option.getD_some] using hb


#print axioms solution
