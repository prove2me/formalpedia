-- Prove2me | solution 1 for ProofsInTheBook.Chapter36.TriangulatedPolygon.exists_3coloring
-- status  : ACCEPTED   (prove)
-- author  : @xiangyazi24
-- created : 2026-09-12T16:44:44.422254+00:00
-- url     : https://prove2.me/submissions/6c588841-2623-4f48-8ec2-a9e36087a139

import Mathlib
import Definitions.Def_ProofsInTheBook_Chapter36


/-!
# Chapter 36: Art galleries

This file proves the combinatorial core of the art gallery theorem: any
abstract polygon triangulation has a 3-coloring, and the smallest color
class gives at most `⌊n / 3⌋` guards meeting every triangle.

Geometry gap audit (2026-05-24): Mathlib has `Geometry.Polygon.Basic`, which
currently provides a vertex-indexed `Polygon`, edge sets, boundary, and
conversion between 3-polygons and affine triangles.  It does not yet provide
the infrastructure needed to state and prove the full geometric art gallery
theorem:

* a definition of a simple polygon as a planar polygonal Jordan curve,
* the polygon interior and the visibility relation from a guard point,
* diagonals lying inside the polygon,
* an ear theorem or equivalent induction step, and
* existence of a triangulation of every simple polygon, together with a proof
  that guards hitting all triangles cover the polygon.

Consequently `chapter36_artgallery_combinatorial` is the closed theorem in
this file.  Extending it to "every simple polygon with `n` vertices is guarded
by `⌊n / 3⌋` vertices" should wait for that geometry layer rather than adding
an unproved triangulation postulate or a placeholder structure here.
-/

namespace ProofsInTheBook.Chapter36



open GuardColor



theorem other_color_neq_left (c1 c2 : GuardColor) : other_color c1 c2 ≠ c1 := by
  cases c1 <;> cases c2 <;> decide

theorem other_color_neq_right (c1 c2 : GuardColor) : other_color c1 c2 ≠ c2 := by
  cases c1 <;> cases c2 <;> decide













lemma valid_coloring_edge {n : ℕ} {T : AbsTriangle n} {c : Fin n → GuardColor}
    (hc : c T.a ≠ c T.b ∧ c T.b ≠ c T.c ∧ c T.a ≠ c T.c) {x y : Fin n}
    (h_edge : Sym2.mk x y ∈ T.edges) : c x ≠ c y := by
  simp only [AbsTriangle.edges, Finset.mem_insert, Finset.mem_singleton] at h_edge
  rcases h_edge with h | h | h
  · apply Sym2.eq.mp at h; cases h
    · exact hc.1
    · exact hc.1.symm
  · apply Sym2.eq.mp at h; cases h
    · exact hc.2.1
    · exact hc.2.1.symm
  · apply Sym2.eq.mp at h; cases h
    · exact hc.2.2
    · exact hc.2.2.symm





















/-! ### Concrete combinatorial witnesses

The remaining frontier in this chapter is the geometric existence of a
`TriangulatedPolygon` for an arbitrary simple polygon (needs Mathlib planar
geometry).  The combinatorial layer is complete, so we can exhibit concrete
inductive witnesses on small vertex sets, validating the inductive constructors
and giving downstream callers ready instances to test against. -/







end ProofsInTheBook.Chapter36

open ProofsInTheBook.Chapter36
open GuardColor

theorem solution {n : ℕ} {S : Finset (AbsTriangle n)}
    (h : TriangulatedPolygon n S) :
    ∃ c : Fin n → GuardColor,
      ∀ T ∈ S, c T.a ≠ c T.b ∧ c T.b ≠ c T.c ∧ c T.a ≠ c T.c := by
  induction h with
  | single T =>
      refine ⟨fun v => if v = T.a then red else if v = T.b then green else blue, ?_⟩
      intro T' hT'
      have h_eq : T' = T := Finset.mem_singleton.mp hT'
      cases h_eq
      have hab' : T.b ≠ T.a := T.hab.symm
      have hbc' : T.c ≠ T.b := T.hbc.symm
      have hac' : T.c ≠ T.a := T.hac.symm
      refine ⟨?_, ?_, ?_⟩ <;> simp [hab', hbc', hac']
  | glue h_ind T v hT_new hShared hFresh ih =>
      obtain ⟨c, hc⟩ := ih
      let c_new := fun x => if x = v then
        other_color (if T.a = v then c T.b else c T.a) (if T.c = v then c T.b else c T.c)
      else c x
      refine ⟨c_new, ?_⟩
      intro T'' hT''
      simp only [Finset.mem_insert] at hT''
      cases hT'' with
      | inl h_eq =>
        -- T'' = T
        rw [h_eq]
        dsimp [c_new]
        have hv : v = T.a ∨ v = T.b ∨ v = T.c := by
          simp only [Finset.mem_insert, Finset.mem_singleton] at hT_new
          exact hT_new
        rcases hShared with ⟨T_s, hT_s_S, e, heT, heT_s, hvne⟩
        have he_color : ∀ x y, e = Sym2.mk x y → c x ≠ c y := by
          intro x y hxy
          subst hxy
          exact valid_coloring_edge (hc T_s hT_s_S) heT_s
        rcases hv with rfl | rfl | rfl
        · -- v = T.a
          have h1 : T.b ≠ T.a := T.hab.symm
          have h2 : T.c ≠ T.a := T.hac.symm
          simp only [h1, h2, if_false, if_true]
          have h_e_is_bc : e = Sym2.mk T.b T.c := by
            simp only [AbsTriangle.edges, Finset.mem_insert, Finset.mem_singleton] at heT
            rcases heT with h | h | h
            · exfalso; apply hvne; rw [h]; exact Sym2.mem_mk_left _ _
            · exact h
            · exfalso; apply hvne; rw [h]; exact Sym2.mem_mk_left _ _
          have hc_bc : c T.b ≠ c T.c := he_color T.b T.c h_e_is_bc
          refine ⟨?_, ?_, ?_⟩
          · exact other_color_neq_left _ _
          · exact hc_bc
          · exact other_color_neq_right _ _
        · -- v = T.b
          have h1 : T.a ≠ T.b := T.hab
          have h2 : T.c ≠ T.b := T.hbc.symm
          simp only [h1, h2, if_false, if_true]
          have h_e_is_ac : e = Sym2.mk T.a T.c := by
            simp only [AbsTriangle.edges, Finset.mem_insert, Finset.mem_singleton] at heT
            rcases heT with h | h | h
            · exfalso; apply hvne; rw [h]; exact Sym2.mem_mk_right _ _
            · exfalso; apply hvne; rw [h]; exact Sym2.mem_mk_left _ _
            · exact h
          have hc_ac : c T.a ≠ c T.c := he_color T.a T.c h_e_is_ac
          refine ⟨?_, ?_, ?_⟩
          · exact (other_color_neq_left (c T.a) (c T.c)).symm
          · exact other_color_neq_right (c T.a) (c T.c)
          · exact hc_ac
        · -- v = T.c
          have h1 : T.a ≠ T.c := T.hac
          have h2 : T.b ≠ T.c := T.hbc
          simp only [h1, h2, if_false, if_true]
          have h_e_is_ab : e = Sym2.mk T.a T.b := by
            simp only [AbsTriangle.edges, Finset.mem_insert, Finset.mem_singleton] at heT
            rcases heT with h | h | h
            · exact h
            · exfalso; apply hvne; rw [h]; exact Sym2.mem_mk_right _ _
            · exfalso; apply hvne; rw [h]; exact Sym2.mem_mk_right _ _
          have hc_ab : c T.a ≠ c T.b := he_color T.a T.b h_e_is_ab
          refine ⟨?_, ?_, ?_⟩
          · exact hc_ab
          · exact (other_color_neq_right (c T.a) (c T.b)).symm
          · exact (other_color_neq_left (c T.a) (c T.b)).symm
      | inr hT''S =>
        -- T'' ∈ S
        have h_v_notin : v ∉ ({T''.a, T''.b, T''.c} : Finset (Fin n)) := hFresh T'' hT''S
        have h1 : T''.a ≠ v := by intro h; apply h_v_notin; simp [h]
        have h2 : T''.b ≠ v := by intro h; apply h_v_notin; simp [h]
        have h3 : T''.c ≠ v := by intro h; apply h_v_notin; simp [h]
        dsimp [c_new]
        simp [h1, h2, h3]
        exact hc T'' hT''S
