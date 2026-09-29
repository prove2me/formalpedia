-- Prove2me | solution 1 for FreeMonoidShuffle.unsh_coassoc
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T01:03:49.451718+00:00
-- url     : https://prove2.me/submissions/e853f691-0176-4821-b9dd-56ea58b50322

import Definitions.Def_Novelty_FreeMonoidShuffle
import Definitions.Def_Novelty_FreeMonoidUnshuffle

open FreeMonoidShuffle

open FreeMonoidShuffle in
/-- **Coassociativity of the unshuffle coproduct**: `(Δ ⊗ id) ∘ Δ = (id ⊗ Δ) ∘ Δ`. -/
theorem solution {X : Type*} [DecidableEq X] (w : List X) : coL w = coR w := by
  induction w with
  | nil => simp [coL, coR, unsh]
  | cons a w ih =>
      -- Every map applied to both sides of the inductive hypothesis stays equal.
      have k : ∀ φ : List X × List X × List X → List X × List X × List X,
          (coL w).map φ = (coR w).map φ := fun φ => by rw [ih]
      -- The three ways the letter `a` can land: front of the first, second, or third part.
      have h1 := k (fun t => (a :: t.1, t.2.1, t.2.2))
      have h2 := k (fun t => (t.1, a :: t.2.1, t.2.2))
      have h3 := k (fun t => (t.1, t.2.1, a :: t.2.2))
      simp only [coL, coR, Multiset.map_bind, Multiset.map_map, Function.comp_def] at h1 h2 h3
      simp only [coL, coR, unsh, Multiset.add_bind, Multiset.bind_map, Multiset.map_add,
        Multiset.bind_add, Multiset.map_map, Function.comp_def]
      rw [h1, h2, h3, add_assoc]
