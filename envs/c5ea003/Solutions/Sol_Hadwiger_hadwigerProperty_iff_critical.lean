-- Prove2me | solution 1 for Hadwiger.hadwigerProperty_iff_critical
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T15:50:37.234203+00:00
-- url     : https://prove2.me/submissions/cb5e1a91-c201-495c-98b4-5af2d13f26e8

import Mathlib
import Definitions.Def_Probability_HadwigerCritical
import Definitions.Def_Probability_HadwigerCriticalEquiv
import Definitions.Def_Probability_HadwigerSmallCases

open Hadwiger SimpleGraph Finset in
theorem solution (k : ℕ) : HadwigerProperty k ↔ HadwigerCriticalProperty k := by
  -- a singleton branch set is connected
  have hsing : ∀ {V : Type} (G : SimpleGraph V) (x : V), SetConnected G {x} := by
    intro V G x
    refine ⟨⟨x, rfl⟩, fun a ha b hb => ?_⟩
    rw [Set.mem_singleton_iff] at ha hb
    subst ha hb
    exact ⟨Walk.nil, fun z hz => by simpa using hz⟩
  -- a complete minor of an induced subgraph is a complete minor of the graph
  have hlift : ∀ {V : Type} (G : SimpleGraph V) (S : Set V),
      CompleteMinor (k + 1) (G.induce S) → CompleteMinor (k + 1) G := by
    intro V G S hmin
    obtain ⟨M⟩ := hmin
    let N : WalkMinorModel (G.induce S) G :=
      { branch := fun v => {v.1}
        branch_nonempty := fun v => ⟨v.1, rfl⟩
        branch_disjoint := by
          intro v w hvw
          rw [Set.disjoint_singleton]
          exact fun h => hvw (Subtype.ext h)
        branch_connected := fun v => hsing G v.1
        edge_lift := by
          intro a b hab
          exact ⟨a.1, rfl, b.1, rfl, hab⟩ }
    exact ⟨(composeModel M.toWalkModel N).toMinorModel⟩
  constructor
  · intro h V _ G hG _
    exact h V G hG
  · intro hc V _ G hG
    classical
    haveI := Fintype.ofFinite V
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · -- `k = 0`: a single vertex already carries a `K₁` minor
      subst hk0
      have hne : Nonempty V := by
        by_contra hV
        exact hG (SimpleGraph.colorable_zero_iff.2 (not_nonempty_iff.1 hV))
      obtain ⟨v⟩ := hne
      let N : WalkMinorModel (⊤ : SimpleGraph (Fin (0 + 1))) G :=
        { branch := fun _ => {v}
          branch_nonempty := fun _ => ⟨v, rfl⟩
          branch_disjoint := by
            intro w w' hww'
            exact absurd (Fin.ext (by have := w.2; have := w'.2; omega)) hww'
          branch_connected := fun _ => hsing G v
          edge_lift := by
            intro a b hab
            exact absurd (Fin.ext (by have := a.2; have := b.2; omega)) hab.ne }
      exact ⟨N.toMinorModel⟩
    -- a minimal non-`k`-colourable vertex set
    have huniv : ¬ ColorableOn G Finset.univ k := by
      rintro ⟨c, hc'⟩
      exact hG ⟨SimpleGraph.Coloring.mk c
        (fun {x y} hxy => hc' x (Finset.mem_univ _) y (Finset.mem_univ _) hxy)⟩
    obtain ⟨S, hS, hmin⟩ := Finset.exists_min_image
      ((Finset.univ : Finset (Finset V)).filter (fun S => ¬ ColorableOn G S k)) Finset.card
      ⟨Finset.univ, by simp [huniv]⟩
    rw [Finset.mem_filter] at hS
    apply hlift G (S : Set V)
    refine hc _ (G.induce (S : Set V)) ?_ ?_
    · -- the induced graph on `S` is not `k`-colourable
      rintro ⟨c⟩
      apply hS.2
      refine ⟨fun x => if hx : x ∈ S then c ⟨x, hx⟩ else ⟨0, hkpos⟩, ?_⟩
      intro x hx y hy hxy
      simp only [dif_pos hx, dif_pos hy]
      exact c.valid (show (G.induce (S : Set V)).Adj ⟨x, hx⟩ ⟨y, hy⟩ from hxy)
    · -- deleting any vertex of `S` makes it colourable, by minimality
      intro v
      have hcol : ColorableOn G (S.erase v.1) k := by
        by_contra hnc
        have h1 := hmin (S.erase v.1) (by simp [hnc])
        have h2 := Finset.card_erase_of_mem (show v.1 ∈ S from v.2)
        have h3 := Finset.card_pos.2 ⟨v.1, v.2⟩
        omega
      obtain ⟨c, hc'⟩ := hcol
      refine ⟨SimpleGraph.Coloring.mk (fun x => c x.1.1) ?_⟩
      intro x y hxy
      have hx : x.1.1 ∈ S.erase v.1 := Finset.mem_erase.2
        ⟨fun h => x.2 (Subtype.ext h), x.1.2⟩
      have hy : y.1.1 ∈ S.erase v.1 := Finset.mem_erase.2
        ⟨fun h => y.2 (Subtype.ext h), y.1.2⟩
      exact hc' _ hx _ hy hxy
