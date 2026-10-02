-- Prove2me | solution 1 for BookSixth.crossing_free_meeting_shared_endpoint
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-17T23:55:40.457922+00:00
-- url     : https://prove2.me/submissions/a332168d-ee35-4718-9495-087fa268b8ed

import Mathlib
import Definitions.Def_BookSixth
open BookSixth

theorem solution {N M : ℕ} (D : PlaneDrawing N M) (e f : Fin M)
    (hfree : ∀ t s : EdgeParameter,
      0 < t.val → t.val < 1 → 0 < s.val → s.val < 1 →
      D.arc e t ≠ D.arc f s)
    (t s : EdgeParameter) (h : D.arc e t = D.arc f s) :
    ∃ v : Fin N, (D.left e = v ∨ D.right e = v) ∧
      (D.left f = v ∨ D.right f = v) ∧ D.arc e t = D.vertex v := by
  have onarc : ∀ (g : Fin M) (u : EdgeParameter) (v : Fin N),
      D.arc g u = D.vertex v → D.left g = v ∨ D.right g = v := by
    intro g u v hg
    by_cases hu0 : u.val = 0
    · have hu : u = ⟨0, by constructor <;> norm_num⟩ := Subtype.ext hu0
      rw [hu, D.start] at hg
      exact Or.inl (D.vertex_injective hg)
    by_cases hu1 : u.val = 1
    · have hu : u = ⟨1, by constructor <;> norm_num⟩ := Subtype.ext hu1
      rw [hu, D.finish] at hg
      exact Or.inr (D.vertex_injective hg)
    · exact False.elim (D.avoid_vertices g u
        (lt_of_le_of_ne u.property.1 (Ne.symm hu0))
        (lt_of_le_of_ne u.property.2 hu1) v hg)
  by_cases ht0 : t.val = 0
  · have ht : t = ⟨0, by constructor <;> norm_num⟩ := Subtype.ext ht0
    have he : D.arc e t = D.vertex (D.left e) := by rw [ht, D.start]
    exact ⟨D.left e, Or.inl rfl, onarc f s (D.left e) (h.symm.trans he), he⟩
  by_cases ht1 : t.val = 1
  · have ht : t = ⟨1, by constructor <;> norm_num⟩ := Subtype.ext ht1
    have he : D.arc e t = D.vertex (D.right e) := by rw [ht, D.finish]
    exact ⟨D.right e, Or.inr rfl, onarc f s (D.right e) (h.symm.trans he), he⟩
  have htpos : 0 < t.val := lt_of_le_of_ne t.property.1 (Ne.symm ht0)
  have htlt : t.val < 1 := lt_of_le_of_ne t.property.2 ht1
  exfalso
  by_cases hs0 : s.val = 0
  · have hs : s = ⟨0, by constructor <;> norm_num⟩ := Subtype.ext hs0
    rw [hs, D.start] at h
    exact D.avoid_vertices e t htpos htlt (D.left f) h
  by_cases hs1 : s.val = 1
  · have hs : s = ⟨1, by constructor <;> norm_num⟩ := Subtype.ext hs1
    rw [hs, D.finish] at h
    exact D.avoid_vertices e t htpos htlt (D.right f) h
  exact hfree t s htpos htlt
    (lt_of_le_of_ne s.property.1 (Ne.symm hs0))
    (lt_of_le_of_ne s.property.2 hs1) h
