-- Prove2me | solution 1 for Arexychen.Erdos180.edgeCount_le_of_isHFree_of_deleteIsolated_isAcyclic
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-09-09T07:22:38.439996+00:00
-- url     : https://prove2.me/submissions/fbc2cffd-14c5-4e5d-b50d-a201c48f1cfa

import Definitions.Def_arexychen_erdos180_core
import Mathlib.Analysis.Asymptotics.Theta
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Tactic
import Theorems.Thm_Arexychen_Erdos180_edgeCount_induce_compl_singleton
import Theorems.Thm_Arexychen_Erdos180_embedsAsSubgraph_of_isAcyclic_of_card_le_minDegree

namespace Arexychen


open Filter
open Asymptotics

noncomputable section

namespace Erdos180

attribute [local instance] SimpleGraph.neighborSetFintype

universe u v

























private theorem isHFree_induce_of_isHFree
    {α : Type u} {β : Type v} {H : SimpleGraph α} {G : SimpleGraph β}
    (s : Set β) (hfree : IsHFree H G) :
    IsHFree H (G.induce s) := by
  intro hemb
  rcases hemb with ⟨f, hf, hmap⟩
  exact hfree ⟨fun x => (f x : β), Subtype.val_injective.comp hf,
    fun _ _ hxy => by simpa [SimpleGraph.induce_adj] using hmap hxy⟩

private theorem embeds_of_deleteIsolated_embeds_of_card_le
    {α : Type u} {β : Type v} [Fintype α] [Fintype β]
    (H : SimpleGraph α) (G : SimpleGraph β)
    (hred : EmbedsAsSubgraph (deleteIsolated H) G)
    (hcard : Fintype.card α ≤ Fintype.card β) :
    EmbedsAsSubgraph H G := by
  classical
  rcases hred with ⟨f, hf, hmap⟩
  rcases Function.Embedding.nonempty_of_card_le hcard with ⟨e : α ↪ β⟩
  have he_support : Function.Injective (fun x : H.support => e (x : α)) :=
    e.injective.comp Subtype.val_injective
  rcases Equiv.Perm.exists_extending_pair
      (fun x : H.support => e (x : α)) f he_support hf with
    ⟨σ, hσ⟩
  let ffull : α → β := fun x => σ (e x)
  refine ⟨ffull, σ.injective.comp e.injective, ?_⟩
  intro x y hxy
  have hx : x ∈ H.support := by
    rw [SimpleGraph.mem_support]
    exact ⟨y, hxy⟩
  have hy : y ∈ H.support := by
    rw [SimpleGraph.mem_support]
    exact ⟨x, hxy.symm⟩
  let sx : H.support := ⟨x, hx⟩
  let sy : H.support := ⟨y, hy⟩
  have hred_xy : (deleteIsolated H).Adj sx sy := by
    simpa [deleteIsolated, sx, sy] using hxy
  have hG_xy : G.Adj (f sx) (f sy) := hmap hred_xy
  have hsx : σ (e x) = f sx := by
    simpa [sx] using hσ sx
  have hsy : σ (e y) = f sy := by
    simpa [sy] using hσ sy
  simpa [ffull, hsx, hsy] using hG_xy

private theorem edgeCount_eq_zero_of_isEmpty
    {β : Type v} (G : SimpleGraph β) [IsEmpty β] :
    edgeCount G = 0 := by
  classical
  have hbot : G = ⊥ := by
    ext x y
    exact False.elim (isEmptyElim x)
  simp [hbot, edgeCount]

private theorem edgeCount_le_of_isHFree_of_deleteIsolated_isAcyclic_aux
    {α : Type u} [Fintype α] (H : SimpleGraph α)
    (hforest : (deleteIsolated H).IsAcyclic) :
    ∀ n : ℕ, ∀ {β : Type v} [Fintype β],
      ∀ (G : SimpleGraph β),
        Fintype.card β = n →
        IsHFree H G →
        edgeCount G ≤ Fintype.card α * Fintype.card β := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro β _ G hβ_card hfree
      classical
      by_cases hβ_nonempty : Nonempty β
      · letI : Nonempty β := hβ_nonempty
        by_cases hlow : G.minDegree < Fintype.card α
        · rcases G.exists_minimal_degree_vertex with ⟨v, hv⟩
          let S : Set β := {v}ᶜ
          let G' : SimpleGraph S := G.induce S
          letI : Fintype S := Fintype.ofFinite S
          letI : DecidableRel G'.Adj := Classical.decRel _
          have hS_lt_card : Fintype.card S < Fintype.card β := by
            exact Fintype.card_subtype_lt
              (p := fun x : β => x ∈ S) (x := v) (by simp [S])
          have hS_lt_n : Fintype.card S < n := by
            omega
          have hfree' : IsHFree H G' :=
            isHFree_induce_of_isHFree S hfree
          have hIH :
              edgeCount G' ≤ Fintype.card α * Fintype.card S :=
            ih (Fintype.card S) hS_lt_n G' rfl hfree'
          have hdeg_le : G.degree v ≤ Fintype.card α := by
            rw [← hv]
            omega
          have hdel :
              edgeCount G' + G.degree v = edgeCount G := by
            simpa [G', S] using edgeCount_induce_compl_singleton G v
          have hS_succ_le : Fintype.card S + 1 ≤ Fintype.card β :=
            Nat.succ_le_of_lt hS_lt_card
          calc
            edgeCount G = edgeCount G' + G.degree v := hdel.symm
            _ ≤ Fintype.card α * Fintype.card S + Fintype.card α :=
              Nat.add_le_add hIH hdeg_le
            _ = Fintype.card α * (Fintype.card S + 1) := by
              rw [Nat.mul_succ]
            _ ≤ Fintype.card α * Fintype.card β :=
              Nat.mul_le_mul_left _ hS_succ_le
        · have hmindeg : Fintype.card α ≤ G.minDegree := le_of_not_gt hlow
          have hcard_full : Fintype.card α ≤ Fintype.card β := by
            exact hmindeg.trans (G.minDegree_lt_card).le
          letI : Fintype H.support := Fintype.ofFinite H.support
          letI : DecidableRel (deleteIsolated H).Adj := Classical.decRel _
          have hsupport_card : Fintype.card H.support ≤ Fintype.card β :=
            (Fintype.card_subtype_le (fun x : α => x ∈ H.support)).trans hcard_full
          have hsupport_deg : Fintype.card H.support ≤ G.minDegree :=
            (Fintype.card_subtype_le (fun x : α => x ∈ H.support)).trans hmindeg
          have hred_emb :
              EmbedsAsSubgraph (deleteIsolated H) G :=
            embedsAsSubgraph_of_isAcyclic_of_card_le_minDegree
              (deleteIsolated H) G hforest hsupport_card hsupport_deg
          exact False.elim
            (hfree (embeds_of_deleteIsolated_embeds_of_card_le H G hred_emb hcard_full))
      · haveI : IsEmpty β := not_nonempty_iff.mp hβ_nonempty
        calc
          edgeCount G = 0 := edgeCount_eq_zero_of_isEmpty G
          _ ≤ Fintype.card α * Fintype.card β := by
            simp

-- `[Fintype α]` is unused in the statement but required by the proof
-- (the witness constant is `Fintype.card α`), hence the linter override.
end Erdos180
end
end Arexychen

section
open Filter
open Asymptotics
attribute [local instance] SimpleGraph.neighborSetFintype
universe u v
open Arexychen.Erdos180 in
set_option linter.unusedFintypeInType false in
theorem solution
    {α : Type u} [Fintype α] (H : SimpleGraph α)
    (hforest : (deleteIsolated H).IsAcyclic) :
    ∃ C : ℕ, ∀ (β : Type v) [Fintype β] (G : SimpleGraph β)
      [DecidableRel G.Adj],
      IsHFree H G → edgeCount G ≤ C * Fintype.card β := by
  classical
  refine ⟨Fintype.card α, ?_⟩
  intro β _ G _ hfree
  exact edgeCount_le_of_isHFree_of_deleteIsolated_isAcyclic_aux
    H hforest (Fintype.card β) G rfl hfree
end
namespace Arexychen
noncomputable section
namespace Erdos180




-- `[Fintype α]` is unused in the statement but required by the proof
-- (it applies the guarded bound above), hence the linter override.


















end Erdos180

end
end Arexychen
