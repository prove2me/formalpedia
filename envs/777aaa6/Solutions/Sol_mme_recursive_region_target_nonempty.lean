-- Prove2me | solution 1 for mme_recursive_region_target_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-13T17:31:22.742209+00:00
-- url     : https://prove2.me/submissions/8091c1cc-3a24-41b2-92cf-5c9309546c78

import Theorems.Thm_mme_prescribed_cell_histogram_nonempty
import Definitions.Def_mme_recursive_x_hash_families

open BigOperators MME.RecursiveYZ
open scoped Classical
set_option autoImplicit false

theorem solution {half R : ℕ} (parent : Fin R → Fin 3 → ℕ) (n : Fin R → ℕ)
    (m : ∀ r, MME.RecursiveThinSplit.Split half (parent r) → ℕ)
    (hmass : ∀ r, ∑ c, m r c = n r) :
    (MME.RecursiveXHash.target (n := n) m).Nonempty := by
  classical
  have hr (r : Fin R) : ∃ a : Fin (n r) → MME.RecursiveThinSplit.Split half (parent r),
      MME.RecursiveThinSplit.HasJointCounts a (m r) := by
    have hsum (u : Unit) : ∑ c, (fun _ : Unit ↦ m r) u c =
        Fintype.card {t : Fin (n r) // (fun _ ↦ ()) t = u} := by
      cases u
      simpa only [Fintype.card_subtype_true, Fintype.card_fin] using hmass r
    obtain ⟨f⟩ := mme_prescribed_cell_histogram_nonempty (fun _ : Fin (n r) ↦ ())
      (fun _ : Unit ↦ m r) (by intro u; cases u; simpa using hmass r)
    refine ⟨f.val, fun c ↦ ?_⟩
    simpa only [count, MME.RecursiveThinSplit.count, true_and] using f.property () c
  choose a ha using hr
  exact ⟨a,Finset.mem_filter.mpr ⟨Finset.mem_univ _,ha⟩⟩
