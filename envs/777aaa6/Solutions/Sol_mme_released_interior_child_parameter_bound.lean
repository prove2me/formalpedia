-- Prove2me | solution 1 for mme_released_interior_child_parameter_bound
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T05:17:17.221802+00:00
-- url     : https://prove2.me/submissions/54318213-5ec0-4974-b04d-2b695fd312f8

import Definitions.Def_mme_released_interior_integer_profiles
open MME MME.ReleasedInterior MME.MoreAsymmetryExactSeed MME.CompleteSplit

private theorem released_parameter_bounds : ∀ (owner : Fin 6) (s : Fin 45),
    ((seed owner s).children.all (fun a => decide (a.2.2 ≤ denominator / 2))) = true := by
  decide +kernel

/-- Every released child parameter is bounded by half the denominator,
including a missing lookup, whose parameter is zero. -/
theorem solution
    (owner : Fin 6) (s : Fin 45) (r : Fin 6) (shape : List ℕ) :
    (((seed owner s).children.find?
      (fun a => a.1 == r.val && a.2.1 == shape)).getD (0, [], 0)).2.2 ≤
        denominator / 2 := by
  cases h : (seed owner s).children.find?
      (fun a => a.1 == r.val && a.2.1 == shape) with
  | none => simp
  | some a =>
    have ha := List.mem_of_find?_eq_some h
    have hb := List.all_eq_true.mp (released_parameter_bounds owner s) a ha
    simpa only [Option.getD_some, decide_eq_true_eq] using hb


#print axioms solution
