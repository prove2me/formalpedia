-- Prove2me | Definitions.Def_AT260939824_UpperCarrierFaces
-- name    : AT260939824_UpperCarrierFaces
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T03:04:27.876411+00:00
-- url     : https://prove2.me/theorems/a8ca27a4-b9a4-4715-b9a8-3b799a5c9aca
-- title:
--   Classification and freeness of upper carrier edges
-- statement:
--   For the height-$(K+1)$ interval carrier, a top-height vertex of an upper triangle is one of its two upper endpoints, and a top-height vertex of a lower fan triangle is its upper-left vertex. For $m\ge1$, the upper endpoints are distinct and determine their cell origin. If a carrier face $s$ contains the two upper vertices of the top cell based at $(r,K)$, then
--   $$s\subseteq\operatorname{upperTriangle}_m(r,K).$$
--   Thus that top horizontal edge is free, and upper edges from different cell origins cannot coincide. These face classifications justify the simultaneous top-triangle collapse.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Sections 2–7, supporting construction for Theorem 1.4 and Proposition 7.1; https://arxiv.org/html/2609.39824v1. Formalization-specific infrastructure in the import closure; individual helper assertions are not represented as separately numbered paper theorems. Original Lean module AbelianTargets/UpperCarrierFaces.lean, selected declaration lines 9-19, 21-33, 35-41, 43-67, 69-114; SHA-256 22d0fd45260b27316ad5c4f9dcf8e51b87acf685e4b7f970fb10cd4a237b0370. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_CarrierCellRealization
import Definitions.Def_AT260939824_CarrierTriangulation
import Definitions.Def_AT260939824_CompressedWords
import Definitions.Def_AT260939824_DigitPathRealization
import Definitions.Def_AT260939824_IntervalCarriers
import Init
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Group.Conj
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Data.Int.Interval
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false

/-! The actual top edges of the finite carrier are free faces of their
presentation-polygon fans. This is a combinatorial statement about the
literal integer-height triangulation, not an assumed deformation. -/

namespace AbelianTargets.IntervalCarriers

theorem top_mem_upperTriangle {m K : ℕ} {A B : ℤ} {c x : Vertex}
    (hc : c ∈ carrierCells m (K+1) A B) (hx : x ∈ upperTriangle m c)
    (hheight : x.2 = K+1) : x = upperLeft c.1 c.2 ∨ x = upperRight m c.1 c.2 := by
  obtain ⟨hv,hj,hr⟩ := Finset.mem_filter.mp hc
  simp only [upperTriangle,Finset.mem_insert,Finset.mem_singleton] at hx
  rcases hx with h | h | h
  · exact Or.inl h
  · have he := congrArg Prod.snd h
    dsimp [lowerVertex] at he
    omega
  · exact Or.inr h

theorem top_mem_lowerTriangle {m K n : ℕ} {A B : ℤ} {c x : Vertex}
    (hc : c ∈ carrierCells m (K+1) A B) (hx : x ∈ lowerTriangle m c n)
    (hheight : x.2 = K+1) : x = upperLeft c.1 c.2 := by
  obtain ⟨hv,hj,hr⟩ := Finset.mem_filter.mp hc
  simp only [lowerTriangle,Finset.mem_insert,Finset.mem_singleton] at hx
  rcases hx with h | h | h
  · exact h
  · have he := congrArg Prod.snd h
    dsimp [lowerVertex] at he
    omega
  · have he := congrArg Prod.snd h
    dsimp [lowerVertex] at he
    omega

theorem upperLeft_ne_upperRight {m : ℕ} (hm : 1 ≤ m) (r : ℤ) (j : ℕ) :
    upperLeft r j ≠ upperRight m r j := by
  intro h
  have he := congrArg Prod.fst h
  have hp : 0 < (m : ℤ)^(j+1) := pow_pos (by exact_mod_cast (show 0 < m by omega)) _
  dsimp [upperLeft,upperRight] at he
  omega

theorem upper_edge_origin_eq {m K : ℕ} (hm : 1 ≤ m) {r q : ℤ}
    (ha : upperLeft r K ∈ upperTriangle m (q,K))
    (hb : upperRight m r K ∈ upperTriangle m (q,K)) : r = q := by
  have hab := upperLeft_ne_upperRight hm r K
  have ha' : upperLeft r K = upperLeft q K ∨ upperLeft r K = upperRight m q K := by
    simp only [upperTriangle,Finset.mem_insert,Finset.mem_singleton] at ha
    rcases ha with h | h | h
    · exact Or.inl h
    · have hh := congrArg Prod.snd h; dsimp [upperLeft,lowerVertex] at hh; omega
    · exact Or.inr h
  have hb' : upperRight m r K = upperLeft q K ∨ upperRight m r K = upperRight m q K := by
    simp only [upperTriangle,Finset.mem_insert,Finset.mem_singleton] at hb
    rcases hb with h | h | h
    · exact Or.inl h
    · have hh := congrArg Prod.snd h; dsimp [upperRight,lowerVertex] at hh; omega
    · exact Or.inr h
  rcases ha' with hau | hav <;> rcases hb' with hbu | hbv
  · exact (hab (hau.trans hbu.symm)).elim
  · exact congrArg Prod.fst hau
  · have h1 := congrArg Prod.fst hav
    have h2 := congrArg Prod.fst hbu
    dsimp [upperLeft,upperRight] at h1 h2
    have hp : 0 < (m : ℤ)^(K+1) := pow_pos (by exact_mod_cast (show 0 < m by omega)) _
    omega
  · exact (hab (hav.trans hbv.symm)).elim

theorem upper_edge_free {m K : ℕ} {A B r : ℤ} (hm : 1 ≤ m)
    {s : Finset Vertex} (hs : CarrierFace m (K+1) A B s)
    (ha : upperLeft r K ∈ s) (hb : upperRight m r K ∈ s) :
    s ⊆ upperTriangle m (r,K) := by
  have hab := upperLeft_ne_upperRight hm r K
  rcases hs with ⟨v,hv,hs⟩ | ⟨u,hu,v,hv,he,hs⟩ | ⟨t,ht,hs⟩
  · have ha' := Finset.mem_singleton.mp (hs ha)
    have hb' := Finset.mem_singleton.mp (hs hb)
    exact (hab (ha'.trans hb'.symm)).elim
  · have ha' := hs ha
    have hb' := hs hb
    simp only [Finset.mem_insert,Finset.mem_singleton] at ha' hb'
    rcases ha' with hau | hav <;> rcases hb' with hbu | hbv
    · exact (hab (hau.trans hbu.symm)).elim
    · rw [←hau,←hbv] at hs
      exact hs.trans (by simp [upperTriangle])
    · rw [←hav,←hbu] at hs
      apply hs.trans
      intro x hx
      simp only [Finset.mem_insert,Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> simp [upperTriangle]
    · exact (hab (hav.trans hbv.symm)).elim
  · obtain ⟨c,hc,ht⟩ := Finset.mem_biUnion.mp ht
    rcases Finset.mem_insert.mp ht with ht | ht
    · subst t
      have ha' := top_mem_upperTriangle hc (hs ha) (by rfl)
      have hb' := top_mem_upperTriangle hc (hs hb) (by rfl)
      rcases ha' with hau | hav <;> rcases hb' with hbu | hbv
      · exact (hab (hau.trans hbu.symm)).elim
      · have hr : r = c.1 := congrArg Prod.fst hau
        have hj : K = c.2 := by have hh := congrArg Prod.snd hau; dsimp [upperLeft] at hh; omega
        have hc' : c = (r,K) := Prod.ext hr.symm hj.symm
        simpa only [hc'] using hs
      · have hj : K = c.2 := by have hh := congrArg Prod.snd hav; dsimp [upperLeft,upperRight] at hh; omega
        have h1 := congrArg Prod.fst hav
        have h2 := congrArg Prod.fst hbu
        dsimp [upperLeft,upperRight] at h1 h2
        rw [←hj] at h1
        have hp : 0 < (m : ℤ)^(K+1) := pow_pos (by exact_mod_cast (show 0 < m by omega)) _
        omega
      · exact (hab (hav.trans hbv.symm)).elim
    · obtain ⟨n,hn,ht⟩ := Finset.mem_image.mp ht
      subst t
      have ha' := top_mem_lowerTriangle hc (hs ha) (by rfl)
      have hb' := top_mem_lowerTriangle hc (hs hb) (by rfl)
      exact (hab (ha'.trans hb'.symm)).elim

end AbelianTargets.IntervalCarriers


