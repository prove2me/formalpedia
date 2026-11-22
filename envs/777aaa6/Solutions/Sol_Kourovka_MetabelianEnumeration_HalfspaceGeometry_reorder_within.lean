-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.HalfspaceGeometry.reorder_within
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:13:55.322106+00:00
-- url     : https://prove2.me/submissions/beaaf763-42e9-4580-aab0-412b52ca1058

import Definitions.Def_Kourovka_Halfspaces_HalfspaceSplitting
import Definitions.Def_Kourovka_Halfspaces_HalfspaceGeometry
import Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceGeometry_exists_safe_step

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.HalfspaceGeometry
variable {X : Type*}
namespace Kourovka.MetabelianEnumeration.HalfspaceGeometry
theorem _root_.solution (f : X → ℝ) (D l u p : ℝ) (xs : List X)
    (hD : ∀ x ∈ xs, |f x| ≤ D) (hwidth : 2 * D ≤ u - l)
    (hp : l ≤ p ∧ p ≤ u)
    (hend : l ≤ p + (xs.map f).sum ∧ p + (xs.map f).sum ≤ u) :
    ∃ ys : List X, ys.Perm xs ∧ Within f l u p ys := by
  classical
  by_cases hn : xs = []
  · subst xs
    exact ⟨[], List.Perm.refl _, hp⟩
  obtain ⟨a, ha, hsafe⟩ := exists_safe_step f D l u p xs hn hD hwidth hp hend
  have hperm : xs.Perm (a :: xs.erase a) := List.perm_cons_erase ha
  have hsum : (xs.map f).sum = f a + ((xs.erase a).map f).sum := by
    simpa only [List.map_cons, List.sum_cons] using (hperm.map f).sum_eq
  obtain ⟨ys, hys, hy⟩ := solution f D l u (p + f a) (xs.erase a)
    (fun x hx => hD x (List.mem_of_mem_erase hx)) hwidth hsafe (by
      rw [add_assoc, ← hsum]
      exact hend)
  exact ⟨a :: ys, (hys.cons a).trans hperm.symm, hp, hy⟩
termination_by xs.length
 decreasing_by
  have hlen := hperm.length_eq
  simp only [List.length_cons] at hlen
  omega
end Kourovka.MetabelianEnumeration.HalfspaceGeometry
