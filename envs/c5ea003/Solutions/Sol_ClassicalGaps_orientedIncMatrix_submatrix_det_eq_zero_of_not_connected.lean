-- Prove2me | solution 1 for ClassicalGaps.orientedIncMatrix_submatrix_det_eq_zero_of_not_connected
-- status  : ACCEPTED   (prove)
-- author  : @Rizwan G Mir
-- created : 2026-09-26T20:32:52.769986+00:00
-- url     : https://prove2.me/submissions/2b8855e4-72a7-4f5c-a31a-05d925123be5

import Mathlib
import Definitions.Def_ClassicalGaps_orientedIncMatrix

open Classical Matrix ClassicalGaps

theorem solution {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (v₀ : V) (F : Finset (Sym2 V)) (hF : F ⊆ G.edgeFinset)
    (e : {x : V // x ≠ v₀} ≃ {x // x ∈ F})
    (hnc : ¬ (SimpleGraph.fromEdgeSet (↑F : Set (Sym2 V))).Connected) :
    (Matrix.of (fun a b : {x : V // x ≠ v₀} => orientedIncMatrix G a.1 ((e b : Sym2 V)))).det = 0 := by
  set H := SimpleGraph.fromEdgeSet (↑F : Set (Sym2 V)) with hH
  obtain ⟨x, hx⟩ : ∃ x, ¬ H.Reachable v₀ x := by
    by_contra h
    push Not at h
    haveI : Nonempty V := ⟨v₀⟩
    exact hnc (SimpleGraph.Connected.mk (fun u w => (h u).symm.trans (h w)))
  have hxv : x ≠ v₀ := by rintro rfl; exact hx (SimpleGraph.Reachable.refl _)
  -- entries vanish off the endpoints
  have hzero : ∀ (a : V) (s : Sym2 V), a ∉ s → orientedIncMatrix G a s = 0 := by
    intro a s has
    unfold orientedIncMatrix
    simp only [Matrix.of_apply]
    rw [dif_neg (fun h => has h.1)]
  -- column sums vanish
  have hsum : ∀ s ∈ G.edgeSet, ∑ v : V, orientedIncMatrix G v s = 0 := by
    intro s he
    induction s using Sym2.ind with
    | _ u w =>
    have hne : u ≠ w := G.ne_of_adj (by rwa [SimpleGraph.mem_edgeSet] at he)
    rw [← Finset.sum_subset (Finset.subset_univ ({u, w} : Finset V)) (fun y _ hy => hzero y _ (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hy
      rw [Sym2.mem_iff]; rintro (h | h) <;> [exact hy.1 h; exact hy.2 h])), Finset.sum_pair hne]
    have hu1 : u ∈ (s(u, w) : Sym2 V) := Sym2.mem_mk_left u w
    have hw1 : w ∈ (s(u, w) : Sym2 V) := Sym2.mem_mk_right u w
    have hother_u : Sym2.Mem.other' hu1 = w := by
      have := Sym2.other_spec' hu1
      rw [Sym2.eq_iff] at this
      rcases this with ⟨-, h⟩ | ⟨h, -⟩
      · exact h
      · exact absurd h hne
    have hother_w : Sym2.Mem.other' hw1 = u := by
      have := Sym2.other_spec' hw1
      rw [Sym2.eq_iff] at this
      rcases this with ⟨h, -⟩ | ⟨-, h⟩
      · exact absurd h hne.symm
      · exact h
    unfold orientedIncMatrix
    simp only [Matrix.of_apply]
    rw [dif_pos ⟨hu1, he⟩, dif_pos ⟨hw1, he⟩, hother_u, hother_w]
    rcases lt_or_gt_of_ne (Fintype.equivFin V |>.injective.ne hne) with h | h <;>
      simp only [Fin.lt_def] at h
    · rw [if_pos h, if_neg (not_lt.mpr h.le)]; ring
    · rw [if_neg (not_lt.mpr h.le), if_pos h]; ring
  let c : {y : V // y ≠ v₀} → ℝ := fun a => if H.Reachable x a.1 then 1 else 0
  have claim : ∀ t : Sym2 V, t ∈ F →
      ∑ a : {y // y ≠ v₀}, c a * orientedIncMatrix G a.1 t = 0 := by
    intro t ht
    induction t using Sym2.ind with
    | _ p q =>
    have hG : s(p, q) ∈ G.edgeSet := by
      have := hF ht; rwa [SimpleGraph.mem_edgeFinset] at this
    have hpq : p ≠ q := G.ne_of_adj (by rwa [SimpleGraph.mem_edgeSet] at hG)
    have hadj : H.Adj p q := by
      rw [hH, SimpleGraph.fromEdgeSet_adj]; exact ⟨by simpa using ht, hpq⟩
    have hiff : ∀ a ∈ s(p, q), (H.Reachable x a ↔ H.Reachable x p) := by
      intro a ha
      rw [Sym2.mem_iff] at ha
      rcases ha with rfl | rfl
      · rfl
      · exact ⟨fun h => h.trans hadj.symm.reachable, fun h => h.trans hadj.reachable⟩
    have hterm : ∀ a : {y // y ≠ v₀}, c a * orientedIncMatrix G a.1 s(p, q) =
        if H.Reachable x p then orientedIncMatrix G a.1 s(p, q) else 0 := by
      intro a
      by_cases ha : a.1 ∈ s(p, q)
      · simp only [c, hiff a.1 ha]; split_ifs <;> simp
      · simp [hzero a.1 _ ha]
    rw [Finset.sum_congr rfl (fun a _ => hterm a)]
    split_ifs with hr
    · have hv : v₀ ∉ s(p, q) := fun hv => hx ((hiff v₀ hv).2 hr).symm
      rw [← Finset.sum_subtype (Finset.univ.erase v₀) (by simp)
        (fun v => orientedIncMatrix G v s(p, q)), Finset.sum_erase (f := fun v => orientedIncMatrix G v s(p, q)) _ (hzero v₀ _ hv)]
      exact hsum _ hG
    · simp
  rw [← Matrix.exists_vecMul_eq_zero_iff]
  refine ⟨c, ?_, ?_⟩
  · intro h
    have := congrFun h ⟨x, hxv⟩
    simp [c] at this
  · funext b
    simp only [Matrix.vecMul, dotProduct, Matrix.of_apply, Pi.zero_apply]
    exact claim _ (e b).2
