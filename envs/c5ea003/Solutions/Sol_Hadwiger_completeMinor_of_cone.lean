-- Prove2me | solution 1 for Hadwiger.completeMinor_of_cone
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T22:31:45.093869+00:00
-- url     : https://prove2.me/submissions/7a2b644c-3c95-4088-b026-ea8edaa82a7a

import Mathlib
import Definitions.Def_Probability_HadwigerK3
import Definitions.Def_Probability_HadwigerMonotone
import Definitions.Def_Probability_HadwigerSmallCases
open Hadwiger MinorTheory.MinorModel in
theorem solution {V : Type*} {G : SimpleGraph V} {n : ℕ} (h : CompleteMinor (n + 1) (cone G)) :
    CompleteMinor n G := by
  classical
  obtain ⟨M⟩ := h
  -- the branch set containing the apex (if any); all others avoid it
  let j0 : Fin (n + 1) :=
    if hj : ∃ j, (Sum.inr () : V ⊕ Unit) ∈ M.branch j then hj.choose else Fin.last n
  have hapex : ∀ j, j ≠ j0 → (Sum.inr () : V ⊕ Unit) ∉ M.branch j := by
    intro j hj hmem
    have hex : ∃ j, (Sum.inr () : V ⊕ Unit) ∈ M.branch j := ⟨j, hmem⟩
    have hj0 : j0 = hex.choose := by simp only [j0, dif_pos hex]
    have hne : j ≠ hex.choose := hj0 ▸ hj
    exact Set.disjoint_left.mp (M.branch_disjoint hne) hmem hex.choose_spec
  -- keep the other `n` branch sets, indexed through `succAbove j0`
  let w : Fin n → Fin (n + 1) := j0.succAbove
  have hinl : ∀ i x, x ∈ M.branch (w i) → ∃ v, x = Sum.inl v := by
    intro i x hx
    cases x with
    | inl v => exact ⟨v, rfl⟩
    | inr u => exact absurd hx (by cases u; exact hapex _ (Fin.succAbove_ne j0 i))
  refine ⟨{ branch := fun i => {v | Sum.inl v ∈ M.branch (w i)},
            branch_nonempty := ?_, branch_disjoint := ?_, branch_connected := ?_,
            edge_lift := ?_ }⟩
  · intro i
    obtain ⟨x, hx⟩ := M.branch_nonempty (w i)
    obtain ⟨v, rfl⟩ := hinl i x hx
    exact ⟨v, hx⟩
  · intro a b hab
    rw [Set.disjoint_left]
    intro v ha hb
    exact Set.disjoint_left.mp
      (M.branch_disjoint (fun h => hab (Fin.succAbove_right_injective h))) ha hb
  · -- the cone's induced graph on an apex-free branch set maps onto `G`'s
    intro i
    obtain ⟨x0, hx0⟩ := M.branch_nonempty (w i)
    obtain ⟨v0, -⟩ := hinl i x0 hx0
    let toV : V ⊕ Unit → V := Sum.elim id (fun _ => v0)
    have htoV : ∀ x ∈ M.branch (w i), Sum.inl (toV x) = x := by
      intro x hx
      obtain ⟨v, rfl⟩ := hinl i x hx
      rfl
    let f : (cone G).induce (M.branch (w i)) →g G.induce {v | Sum.inl v ∈ M.branch (w i)} :=
      { toFun := fun x => ⟨toV x.1, by
          show Sum.inl (toV x.1) ∈ M.branch (w i)
          rw [htoV x.1 x.2]
          exact x.2⟩
        map_rel' := by
          intro x y hxy
          obtain ⟨u, hu⟩ := hinl i x.1 x.2
          obtain ⟨v, hv⟩ := hinl i y.1 y.2
          simp only [SimpleGraph.comap_adj, Function.Embedding.coe_subtype] at hxy ⊢
          rw [hu, hv] at hxy ⊢
          exact hxy }
    refine SimpleGraph.Connected.map f ?_ (M.branch_connected (w i))
    rintro ⟨v, hv⟩
    exact ⟨⟨Sum.inl v, hv⟩, rfl⟩
  · -- edges between kept branch sets are realised by `G`-edges
    intro a b hab
    have hab' : (⊤ : SimpleGraph (Fin (n + 1))).Adj (w a) (w b) := by
      rw [SimpleGraph.top_adj]
      exact fun h => ((SimpleGraph.top_adj _ _).mp hab) (Fin.succAbove_right_injective h)
    obtain ⟨x, hx, y, hy, hxy⟩ := M.edge_lift hab'
    obtain ⟨u, rfl⟩ := hinl a x hx
    obtain ⟨v, rfl⟩ := hinl b y hy
    exact ⟨u, hx, v, hy, hxy⟩
