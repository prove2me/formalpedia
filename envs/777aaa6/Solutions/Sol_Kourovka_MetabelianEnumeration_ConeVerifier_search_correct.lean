-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ConeVerifier.search_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:05:04.744228+00:00
-- url     : https://prove2.me/submissions/7e9839b7-e11f-4925-86ef-6945062cd079

import Definitions.Def_Kourovka_Polyhedral_FourierMotzkin
import Definitions.Def_Kourovka_Polyhedral_ConeVerifier
import Theorems.Thm_Kourovka_MetabelianEnumeration_ConeVerifier_supportRow_iff
import Theorems.Thm_Kourovka_MetabelianEnumeration_FourierMotzkin_check_correct


set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ConeVerifier
open FourierMotzkin
namespace Kourovka.MetabelianEnumeration.ConeVerifier
theorem _root_.solution {n : ℕ} (epsilon : ℚ) (supports : Supports n)
    (rows : List (Row n)) : search n epsilon supports rows = true ↔
    ∃ x : Fin n → ℝ, Satisfies rows x ∧
      ∀ support ∈ supports, ∃ u ∈ support, dot u x ≤ epsilon := by
  induction supports generalizing rows with
  | nil => simpa [search, Feasible] using check_correct n rows ℝ
  | cons support rest ih =>
    simp only [search, List.any_eq_true, ih]
    constructor
    · rintro ⟨u, hu, x, hx, hrest⟩
      have hu' := (supportRow_iff u epsilon x).mp (hx _ List.mem_cons_self)
      refine ⟨x, fun r hr => hx r (List.mem_cons_of_mem _ hr), ?_⟩
      intro s hs
      rcases List.mem_cons.mp hs with rfl | hs
      · exact ⟨u, hu, hu'⟩
      · exact hrest s hs
    · rintro ⟨x, hx, hs⟩
      obtain ⟨u, hu, hu'⟩ := hs support List.mem_cons_self
      refine ⟨u, hu, x, ?_, fun s h => hs s (List.mem_cons_of_mem _ h)⟩
      intro r hr
      rcases List.mem_cons.mp hr with rfl | hr
      · exact (supportRow_iff u epsilon x).mpr hu'
      · exact hx r hr
end Kourovka.MetabelianEnumeration.ConeVerifier
