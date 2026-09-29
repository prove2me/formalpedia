-- Prove2me | solution 1 for mme_released_interior_112_child_marginal_exact
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T04:59:09.340407+00:00
-- url     : https://prove2.me/submissions/81cde14b-c275-41c3-a650-7857e4921286

import Theorems.Thm_mme_released_interior_112_child_marginal
open MME MME.ReleasedInterior MME.MoreAsymmetryExactSeed MME.CompleteSplit

private theorem released_parameter_bounds : ∀ (owner : Fin 6) (s : Fin 45),
    ((seed owner s).children.all (fun a => decide (a.2.2 ≤ denominator / 2))) = true := by
  decide +kernel

/-- Every released child parameter is bounded by half the denominator,
including a missing lookup, whose parameter is zero. -/
theorem mme_released_interior_child_parameter_bound
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

/-- The canonical 112 marginal formula holds for every released recipe,
with its parameter bound discharged against the exact released data. -/
theorem solution
    (owner : Fin 6) (s : Fin 45) (r : Fin 6) (c : Split s) (z : Fin 3)
    (hshape : ∀ i : Fin 3, (c.val i).val = if i = z then 2 else 1) :
    let p := (((seed owner s).children.find?
      (fun a => a.1 == r.val && a.2.1 == sourceShape owner c)).getD (0, [], 0)).2.2
    ∀ (i : Fin 3) (w : CompleteWord 2),
      childMarginal owner s r c i w =
        if i = z then
          if w = ![0, 2] ∨ w = ![2, 0] then p
          else if w = ![1, 1] then denominator - 2 * p else 0
        else if w = ![0, 1] ∨ w = ![1, 0] then denominator / 2 else 0 := by
  exact mme_released_interior_112_child_marginal owner s r c z hshape
    (mme_released_interior_child_parameter_bound owner s r (sourceShape owner c))


#print axioms solution
