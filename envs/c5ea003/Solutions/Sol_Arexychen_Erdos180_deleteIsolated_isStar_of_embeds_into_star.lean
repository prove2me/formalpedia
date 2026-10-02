-- Prove2me | solution 1 for Arexychen.Erdos180.deleteIsolated_isStar_of_embeds_into_star
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-09-09T07:28:36.055684+00:00
-- url     : https://prove2.me/submissions/b478e9db-e473-4a3b-b491-ccfbb6acfcbe

import Definitions.Def_arexychen_erdos180_core
import Mathlib.Analysis.Asymptotics.Theta
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Tactic

namespace Arexychen


open Filter
open Asymptotics

noncomputable section

namespace Erdos180

universe u v w



end Erdos180
end
end Arexychen

section
open Filter
open Asymptotics
universe u v w
open Arexychen.Erdos180 in
/-- If a graph with at least one edge embeds into a star, then its reduced
non-isolated graph is a star. -/
theorem solution
    {α : Type u} {β : Type v}
    {H : SimpleGraph α} {c : β}
    (hemb : EmbedsAsSubgraph H (starGraph c))
    (hne : ∃ x y : α, H.Adj x y) :
    IsStar (deleteIsolated H) := by
  rcases hemb with ⟨f, hf, hmap⟩
  rcases hne with ⟨x₀, y₀, hxy₀⟩
  have hstar₀ : (starGraph c).Adj (f x₀) (f y₀) := hmap hxy₀
  have hcenter_exists : ∃ z : α, z ∈ H.support ∧ f z = c := by
    rcases hstar₀ with h | h
    · exact ⟨x₀, ⟨y₀, hxy₀⟩, h.1⟩
    · exact ⟨y₀, ⟨x₀, hxy₀.symm⟩, h.1⟩
  rcases hcenter_exists with ⟨z, hz_support, hfz⟩
  let center : H.support := ⟨z, hz_support⟩
  have eq_center_of_image_eq
      (u : H.support) (hu : f (u : α) = c) :
      u = center := by
    apply Subtype.ext
    exact hf (hu.trans hfz.symm)
  have image_ne_center_of_ne
      (u : H.support) (hu : u ≠ center) :
      f (u : α) ≠ c := by
    intro hfu
    exact hu (eq_center_of_image_eq u hfu)
  have adj_center_of_ne_center
      (u : H.support) (hu : u ≠ center) :
      H.Adj center.1 u.1 := by
    rcases u.2 with ⟨w, huw⟩
    have hstar : (starGraph c).Adj (f (u : α)) (f w) := hmap huw
    rcases hstar with h | h
    · exact False.elim ((image_ne_center_of_ne u hu) h.1)
    · have hw_eq : w = center.1 := by
        exact hf (h.1.trans hfz.symm)
      have huw' : H.Adj u.1 center.1 := by
        simpa [hw_eq] using huw
      exact huw'.symm
  refine ⟨center, ?_⟩
  ext u v
  constructor
  · intro huv
    have hH : H.Adj u.1 v.1 := by
      simpa [deleteIsolated] using huv
    have hstar : (starGraph c).Adj (f (u : α)) (f (v : α)) := hmap hH
    rcases hstar with h | h
    · have hu : u = center := eq_center_of_image_eq u h.1
      exact Or.inl ⟨hu, by
        intro hv
        exact huv.ne (hu.trans hv.symm)⟩
    · have hv : v = center := eq_center_of_image_eq v h.1
      exact Or.inr ⟨hv, by
        intro hu
        exact huv.ne (hu.trans hv.symm)⟩
  · intro huv
    rcases huv with h | h
    · rcases h with ⟨hu, hv_ne⟩
      subst hu
      have hcv : H.Adj center.1 v.1 :=
        adj_center_of_ne_center v hv_ne
      simpa [deleteIsolated] using hcv
    · rcases h with ⟨hv, hu_ne⟩
      subst hv
      have hcu : H.Adj center.1 u.1 :=
        adj_center_of_ne_center u hu_ne
      simpa [deleteIsolated] using hcu.symm
end
namespace Arexychen
noncomputable section
namespace Erdos180




end Erdos180

end
end Arexychen
