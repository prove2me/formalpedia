-- Prove2me | solution 1 for TriangularForest.DecomposesIntoTwo.comap
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T10:58:13.578862+00:00
-- url     : https://prove2.me/submissions/ce5bd66d-0225-47bb-b647-6c92b07d2eeb

import Mathlib
import Definitions.Def_Logic_TriangularForest_ClassProperties
import Definitions.Def_Logic_TriangularForest_Decomposition
open TriangularForest SimpleGraph in
theorem solution {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W} (f : W ↪ V)
    (hG : DecomposesIntoTwo G) (hH : H ≤ G.comap f) : DecomposesIntoTwo H := by
  obtain ⟨G₁, G₂, h1, h2, hdisj, hsup⟩ := hG
  -- pulling a triangular forest back and meeting with `H` stays a triangular forest
  have key : ∀ K : SimpleGraph V, IsTriangularForest K → IsTriangularForest (H ⊓ K.comap f) := by
    intro K hK v c hc
    let φ : (H ⊓ K.comap f) →g K :=
      { toFun := f
        map_rel' := fun {a b} hab => (inf_le_right : (H ⊓ K.comap f) ≤ K.comap f) hab }
    have hcy : (c.map φ).IsCycle :=
      (SimpleGraph.Walk.map_isCycle_iff_of_injective f.injective).mpr hc
    have hlen : (c.map φ).length = c.length := by simp
    rw [← hlen]
    exact hK _ hcy
  refine ⟨H ⊓ G₁.comap f, H ⊓ G₂.comap f, key G₁ h1, key G₂ h2, ?_, ?_⟩
  · -- disjointness is inherited from `G₁`, `G₂`
    have hcd : Disjoint (G₁.comap f) (G₂.comap f) := by
      rw [disjoint_iff] at hdisj ⊢
      have hci : (G₁.comap f) ⊓ (G₂.comap f) = (G₁ ⊓ G₂).comap f :=
        SimpleGraph.adj_inj.mp rfl
      rw [hci, hdisj]
      exact SimpleGraph.adj_inj.mp rfl
    exact hcd.mono inf_le_right inf_le_right
  · -- and the two pieces cover `H` because `H ≤ G.comap f`
    have hcs : (G₁.comap f) ⊔ (G₂.comap f) = (G₁ ⊔ G₂).comap f :=
      SimpleGraph.adj_inj.mp rfl
    rw [← inf_sup_left, hcs, hsup]
    exact inf_eq_left.mpr hH
