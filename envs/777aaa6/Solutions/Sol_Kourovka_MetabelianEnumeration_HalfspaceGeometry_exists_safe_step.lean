-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.HalfspaceGeometry.exists_safe_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:12:41.654427+00:00
-- url     : https://prove2.me/submissions/73805769-32d0-4b57-9f8d-bf72684b0edc

import Definitions.Def_Kourovka_Halfspaces_HalfspaceSplitting
import Definitions.Def_Kourovka_Halfspaces_HalfspaceGeometry

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.HalfspaceGeometry
variable {X : Type*}
namespace Kourovka.MetabelianEnumeration.HalfspaceGeometry
theorem _root_.solution (f : X → ℝ) (D l u p : ℝ) (xs : List X)
    (hne : xs ≠ []) (hD : ∀ x ∈ xs, |f x| ≤ D)
    (hwidth : 2 * D ≤ u - l) (hp : l ≤ p ∧ p ≤ u)
    (hend : l ≤ p + (xs.map f).sum ∧ p + (xs.map f).sum ≤ u) :
    ∃ x ∈ xs, l ≤ p + f x ∧ p + f x ≤ u := by
  by_contra! h
  obtain ⟨a, ys, rfl⟩ := List.exists_cons_of_ne_nil hne
  have hbound : ∀ x ∈ a :: ys, -D ≤ f x ∧ f x ≤ D :=
    fun x hx => abs_le.mp (hD x hx)
  by_cases hnear : p - l ≤ D
  · have hneg : ∀ x ∈ a :: ys, p + f x < l := by
      intro x hx
      by_contra! hxlo
      have hxhi : p + f x ≤ u := by have := (hbound x hx).2; linarith
      exact (not_lt_of_ge hxhi) (h x hx hxlo)
    have htail : (ys.map f).sum ≤ 0 := by
      have hterm : ∀ x ∈ ys, f x ≤ 0 := by
        intro x hx
        have := hneg x (List.mem_cons_of_mem _ hx)
        linarith [hp.1]
      clear hneg hbound hD h hend hne
      induction ys with
      | nil => simp
      | cons z zs ih =>
        simp only [List.map_cons, List.sum_cons]
        have hz := hterm z List.mem_cons_self
        have hs := ih (fun x hx => hterm x (List.mem_cons_of_mem _ hx))
        linarith
    have := hneg a (List.mem_cons_self)
    simp only [List.map_cons, List.sum_cons] at hend
    linarith [hend.1]
  · have hpos : ∀ x ∈ a :: ys, u < p + f x := by
      intro x hx
      apply h x hx
      have := (hbound x hx).1
      linarith
    have htail : 0 ≤ (ys.map f).sum := List.sum_nonneg fun z hz => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hz
      have := hpos x (List.mem_cons_of_mem _ hx)
      linarith [hp.2]
    have := hpos a (List.mem_cons_self)
    simp only [List.map_cons, List.sum_cons] at hend
    linarith [hend.2]
end Kourovka.MetabelianEnumeration.HalfspaceGeometry
