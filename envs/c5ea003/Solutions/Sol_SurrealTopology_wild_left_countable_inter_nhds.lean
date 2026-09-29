-- Prove2me | solution 1 for SurrealTopology.wild_left_countable_inter_nhds
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-22T07:46:49.790005+00:00
-- url     : https://prove2.me/submissions/3a7a7667-5336-4bdf-a205-c6f88dc1b3ed

import Mathlib
import Definitions.Def_Geometry_PosetTheory_SurrealTopology

open Set Filter Topology
open SurrealTopology

/-- Match the target's accumulated preamble `variable` telescope
(LinearOrder once, then LinearOrder+TopologicalSpace+OrderTopology twice). -/
theorem solution {α : Type*} [LinearOrder α]
    [LinearOrder α] [TopologicalSpace α] [OrderTopology α]
    [LinearOrder α] [TopologicalSpace α] [OrderTopology α]
    {x : α} (hx : ¬HasCountableLeftCof x)
    {U : ℕ → Set α} (hU : ∀ n, U n ∈ nhds x) :
    ∃ b, b < x ∧ ∀ z, b < z → z < x → ∀ n, z ∈ U n := by
  have hne : ∃ a, a < x := by
    by_contra H
    refine hx ?_
    intro hex
    exact H.elim hex
  have hb_ex : ∀ n, ∃ b, b < x ∧ Ioo b x ⊆ U n := by
    intro n
    obtain ⟨l, hl, hlU⟩ := exists_Ioc_subset_of_mem_nhds (hU n) hne
    exact ⟨l, hl, (Ioo_subset_Ioc_self.trans hlU)⟩
  choose b hb_lt hb_sub using hb_ex
  obtain ⟨y, hy_lt, hy_bound⟩ : ∃ y, y < x ∧ ∀ n, b n < y := by
    contrapose! hx
    intro _
    exact ⟨b, hb_lt, hx⟩
  refine ⟨y, hy_lt, ?_⟩
  intro z hz₁ hz₂ n
  exact hb_sub n ⟨(hy_bound n).trans hz₁, hz₂⟩
