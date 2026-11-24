-- Prove2me | Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_outside_component_attachment
-- name    : WrittenOnTheWallII.GraphConjecture84.outside_component_attachment
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T05:30:01.062591+00:00
-- url     : https://prove2.me/theorems/9342041b-c831-4795-85dc-b647a72c7813
-- title:
--   Graph Conjecture84: outside component attachment
-- statement:
--   If outside components have unique core contacts, each has a contact which
--   separates it from every other core vertex.
--
--   Source: https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L1314-L1359
-- source:
--   https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L1314-L1359

module
public import Mathlib
public import Definitions.Def_Wowii84_LargestInducedTree
public import Definitions.Def_Wowii84_Main
set_option autoImplicit false
@[expose] public section
public section
open WrittenOnTheWallII WrittenOnTheWallII.GraphConjecture84
open SimpleGraph
variable {α : Type*} [Fintype α] [DecidableEq α]

theorem WrittenOnTheWallII.GraphConjecture84.outside_component_attachment {G : SimpleGraph α} (hG : G.Connected)
    (K : Finset α) (hK : K.Nonempty)
    (huniq : ∀ (z w : ↥((K : Set α)ᶜ)),
      (G.induce (K : Set α)ᶜ).Reachable z w →
      ∀ {a b : α}, a ∈ K → b ∈ K → G.Adj a z → G.Adj b w → a = b)
    (z : ↥((K : Set α)ᶜ)) :
    ∃ (c : α) (hc : c ∈ K), ∃ w : ↥((K : Set α)ᶜ),
      (G.induce (K : Set α)ᶜ).Reachable z w ∧ G.Adj c w ∧
      ∀ (v : α) (hv : v ∈ K) (hvc : v ≠ c),
        ¬ (G.induce ({c}ᶜ : Set α)).Reachable
          ⟨z, by simpa using (show (z : α) ≠ c from fun heq => z.property (heq.symm ▸ hc))⟩
          ⟨v, by simpa using hvc⟩ := by sorry
