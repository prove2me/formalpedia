-- Prove2me | solution 1 for SurrealTopology.tame_implies_countably_generated_nhds
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T12:57:15.23427+00:00
-- url     : https://prove2.me/submissions/329af056-78d9-4036-a92a-85a8b6a87fef

import Mathlib
import Definitions.Def_Geometry_PosetTheory_SurrealTopology

open Set Filter Topology SurrealTopology in
theorem solution {α : Type*} [LinearOrder α] [LinearOrder α] [TopologicalSpace α]
    [OrderTopology α] [LinearOrder α] [TopologicalSpace α] [OrderTopology α] [LinearOrder α]
    [TopologicalSpace α] [OrderTopology α] {x : α}
    (hL : ∃ S : ℕ → α, (∀ n, S n < x) ∧ ∀ y, y < x → ∃ n, y ≤ S n)
    (hR : ∃ S : ℕ → α, (∀ n, x < S n) ∧ ∀ y, x < y → ∃ n, S n ≤ y) :
    (nhds x).IsCountablyGenerated := by
  obtain ⟨S, hS, hScof⟩ := hL
  obtain ⟨T, hT, hTcof⟩ := hR
  have hb := nhds_basis_Ioo' (a := x) ⟨S 0, hS 0⟩ ⟨T 0, hT 0⟩
  have hb' : (nhds x).HasBasis (fun _ : ℕ × ℕ => True) fun nm => Ioo (S nm.1) (T nm.2) := by
    refine hb.to_hasBasis (fun ab hab => ?_) (fun nm _ => ⟨(S nm.1, T nm.2), ⟨hS _, hT _⟩, le_rfl⟩)
    obtain ⟨n, hn⟩ := hScof ab.1 hab.1
    obtain ⟨m, hm⟩ := hTcof ab.2 hab.2
    exact ⟨(n, m), trivial, Ioo_subset_Ioo hn hm⟩
  exact hb'.isCountablyGenerated
