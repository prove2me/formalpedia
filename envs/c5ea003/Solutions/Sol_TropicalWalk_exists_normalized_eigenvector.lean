-- Prove2me | solution 1 for TropicalWalk.exists_normalized_eigenvector
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T07:34:18.033527+00:00
-- url     : https://prove2.me/submissions/a02e569e-60e5-4f0a-81e2-643ffb2b51dc

import Mathlib
import Definitions.Def_Bridges_TropicalWalkPerron

open Finset TropicalWalk in
theorem solution {V : Type*} [Fintype V] [Nonempty V] {A : V → V → ℝ}
    (H1 : ∀ m : ℕ, 1 ≤ m → ∀ p : ℕ → V, p 0 = p m → walkW A p m ≤ 0)
    {c : V} {L : ℕ} (hL : L < Fintype.card V) (hc : bestW A L c c = 0) :
    ∃ v : V → ℝ, ∀ i : V,
      Finset.univ.sup' Finset.univ_nonempty (fun j => A i j + v j) = v i := by
  classical
  set N := Fintype.card V with hN
  have hstep : ∀ m i t, bestW A (m + 1) i t
      = univ.sup' univ_nonempty (fun l => bestW A m i l + A l t) := fun _ _ _ => rfl
  -- (1) first-step decomposition of best walks
  have hfirst : ∀ k i t, bestW A (k + 1) i t
      = univ.sup' univ_nonempty (fun j => A i j + bestW A k j t) := by
    intro k
    induction k with
    | zero =>
      intro i t
      rfl
    | succ k ih =>
      intro i t
      rw [hstep (k + 1) i t]
      apply le_antisymm
      · apply Finset.sup'_le
        intro l _
        rw [ih i l]
        have h1 : ∀ j, A i j + bestW A k j l + A l t
            ≤ univ.sup' univ_nonempty (fun j => A i j + bestW A (k + 1) j t) := by
          intro j
          have h2 : bestW A k j l + A l t ≤ bestW A (k + 1) j t := by
            rw [hstep k j t]
            exact Finset.le_sup' (fun l => bestW A k j l + A l t) (mem_univ l)
          have h3 := Finset.le_sup' (fun j => A i j + bestW A (k + 1) j t) (mem_univ j)
          linarith
        have h4 : univ.sup' univ_nonempty (fun j => A i j + bestW A k j l)
            ≤ univ.sup' univ_nonempty (fun j => A i j + bestW A (k + 1) j t) - A l t :=
          Finset.sup'_le _ _ fun j _ => by linarith [h1 j]
        linarith
      · apply Finset.sup'_le
        intro j _
        rw [hstep k j t]
        have h1 : ∀ l, A i j + (bestW A k j l + A l t)
            ≤ univ.sup' univ_nonempty (fun l => bestW A (k + 1) i l + A l t) := by
          intro l
          have h2 : A i j + bestW A k j l ≤ bestW A (k + 1) i l := by
            rw [ih i l]
            exact Finset.le_sup' (fun j => A i j + bestW A k j l) (mem_univ j)
          have h3 := Finset.le_sup' (fun l => bestW A (k + 1) i l + A l t) (mem_univ l)
          linarith
        have h4 : univ.sup' univ_nonempty (fun l => bestW A k j l + A l t)
            ≤ univ.sup' univ_nonempty (fun l => bestW A (k + 1) i l + A l t) - A i j :=
          Finset.sup'_le _ _ fun l _ => by linarith [h1 l]
        linarith
  -- (2) walks: every walk is bounded by `bestW`, and `bestW` is attained
  have hbound : ∀ m (p : ℕ → V), walkW A p (m + 1) ≤ bestW A m (p 0) (p (m + 1)) := by
    intro m
    induction m with
    | zero =>
      intro p
      simp [walkW, bestW]
    | succ m ih =>
      intro p
      have e : walkW A p (m + 1 + 1) = walkW A p (m + 1) + A (p (m + 1)) (p (m + 1 + 1)) := by
        unfold walkW
        rw [Finset.sum_range_succ]
      rw [e, hstep m (p 0) (p (m + 1 + 1))]
      have h1 := ih p
      have h2 := Finset.le_sup' (fun l => bestW A m (p 0) l + A l (p (m + 1 + 1)))
        (mem_univ (p (m + 1)))
      simp only at h2
      linarith
  have hattain : ∀ m i t, ∃ p : ℕ → V, p 0 = i ∧ p (m + 1) = t ∧
      walkW A p (m + 1) = bestW A m i t := by
    intro m
    induction m with
    | zero =>
      intro i t
      refine ⟨fun s => if s = 0 then i else t, by simp, by simp, ?_⟩
      simp [walkW, bestW]
    | succ m ih =>
      intro i t
      obtain ⟨l, -, hl⟩ := Finset.exists_mem_eq_sup' univ_nonempty
        (fun l => bestW A m i l + A l t)
      obtain ⟨p, hp0, hpm, hpw⟩ := ih i l
      refine ⟨fun s => if s ≤ m + 1 then p s else t, by simp [hp0], by simp, ?_⟩
      have e1 : walkW A (fun s => if s ≤ m + 1 then p s else t) (m + 1) = walkW A p (m + 1) := by
        unfold walkW
        refine Finset.sum_congr rfl fun s hs => ?_
        have hs' := Finset.mem_range.1 hs
        simp only [show s ≤ m + 1 by omega, show s + 1 ≤ m + 1 by omega, if_true]
      have e2 : walkW A (fun s => if s ≤ m + 1 then p s else t) (m + 1 + 1)
          = walkW A (fun s => if s ≤ m + 1 then p s else t) (m + 1) + A l t := by
        unfold walkW
        rw [Finset.sum_range_succ]
        simp only [le_refl, if_true, show ¬ (m + 1 + 1 ≤ m + 1) by omega, if_false, hpm]
      rw [e2, e1, hpw, hstep m i t, hl]
  -- (3) cycle removal: `N + 1` edges never beat fewer than `N + 1` edges
  have hN0 : 0 < N := Fintype.card_pos
  have hrange : (range N).Nonempty := nonempty_range_iff.2 hN0.ne'
  set v : V → ℝ := fun i => (range N).sup' hrange (fun k => bestW A k i c) with hv
  have hcut : ∀ i, bestW A N i c ≤ v i := by
    intro i
    obtain ⟨p, hp0, hpN, hpw⟩ := hattain N i c
    obtain ⟨x, y, hxy, hpxy⟩ := Fintype.exists_ne_map_eq_of_card_lt
      (fun s : Fin (N + 1) => p s) (by simp [hN])
    -- order the repeated positions `a < b ≤ N`
    have key : ∀ a b : ℕ, a < b → b ≤ N → p a = p b → bestW A N i c ≤ v i := by
      intro a b hab hbN hpab
      set d := b - a with hd
      set M := N - d with hM
      set q : ℕ → V := fun s => if s ≤ a then p s else p (s + d) with hq
      have hq0 : q 0 = i := by simp [hq, hp0]
      have hqM : q (M + 1) = c := by
        simp only [hq, show ¬ (M + 1 ≤ a) by omega, if_false]
        rw [show M + 1 + d = N + 1 by omega, hpN]
      -- the removed loop has nonpositive weight
      have hloop : ∑ s ∈ range d, A (p (a + s)) (p (a + s + 1)) ≤ 0 := by
        have h1 := H1 d (by omega) (fun s => p (a + s)) (by simp [hpab, show a + d = b by omega])
        unfold walkW at h1
        simpa [add_assoc] using h1
      -- splitting the long walk
      have hsplit : walkW A p (N + 1) = walkW A q (M + 1)
          + ∑ s ∈ range d, A (p (a + s)) (p (a + s + 1)) := by
        unfold walkW
        have e1 : N + 1 = a + (d + (M + 1 - a)) := by omega
        have e2 : M + 1 = a + (M + 1 - a) := by omega
        rw [e1, Finset.sum_range_add, Finset.sum_range_add]
        conv_rhs => rw [e2, Finset.sum_range_add]
        have hA : ∑ s ∈ range a, A (q s) (q (s + 1)) = ∑ s ∈ range a, A (p s) (p (s + 1)) := by
          refine Finset.sum_congr rfl fun s hs => ?_
          have hs' := Finset.mem_range.1 hs
          simp only [hq, show s ≤ a by omega, show s + 1 ≤ a by omega, if_true]
        have hB : ∑ s ∈ range (M + 1 - a), A (q (a + s)) (q (a + s + 1))
            = ∑ s ∈ range (M + 1 - a), A (p (a + (d + s))) (p (a + (d + s) + 1)) := by
          refine Finset.sum_congr rfl fun s _ => ?_
          have h1 : q (a + s) = p (a + (d + s)) := by
            rcases Nat.eq_zero_or_pos s with h0 | h0
            · subst h0
              simp only [hq, add_zero, le_refl, if_true]
              rw [hpab, show a + d = b by omega]
            · simp only [hq, show ¬ (a + s ≤ a) by omega, if_false]
              congr 1
              omega
          have h2 : q (a + s + 1) = p (a + (d + s) + 1) := by
            simp only [hq, show ¬ (a + s + 1 ≤ a) by omega, if_false]
            congr 1
            omega
          rw [h1, h2]
        rw [hA, hB]
        simp only [add_assoc]
        ring
      have h1 := hbound M q
      rw [hq0, hqM] at h1
      have h2 : bestW A M i c ≤ v i :=
        Finset.le_sup' (fun k => bestW A k i c) (Finset.mem_range.2 (by omega))
      rw [← hpw]
      linarith
    have hx := x.isLt
    have hy := y.isLt
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hxy) with h | h
    · exact key x y h (by omega) hpxy
    · exact key y x h (by omega) hpxy.symm
  -- (4) the eigen-equation
  refine ⟨v, fun i => le_antisymm ?_ ?_⟩
  · apply Finset.sup'_le
    intro j _
    obtain ⟨k, hk, hkv⟩ := Finset.exists_mem_eq_sup' hrange (fun k => bestW A k j c)
    have hk' := Finset.mem_range.1 hk
    have h1 : A i j + bestW A k j c ≤ bestW A (k + 1) i c := by
      rw [hfirst k i c]
      exact Finset.le_sup' (fun j => A i j + bestW A k j c) (mem_univ j)
    have h2 : bestW A (k + 1) i c ≤ v i := by
      rcases Nat.lt_or_ge (k + 1) N with h | h
      · exact Finset.le_sup' (fun k => bestW A k i c) (Finset.mem_range.2 h)
      · rw [show k + 1 = N by omega]
        exact hcut i
    show A i j + v j ≤ v i
    rw [hv]
    simp only
    rw [hkv]
    linarith
  · obtain ⟨k, hk, hkv⟩ := Finset.exists_mem_eq_sup' hrange (fun k => bestW A k i c)
    have hk' := Finset.mem_range.1 hk
    show v i ≤ _
    rw [hv]
    simp only
    rw [hkv]
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · -- a direct edge to `c`, padded by the zero loop at `c`
      subst h0
      have hvc : 0 ≤ v c := by
        rw [← hc]
        exact Finset.le_sup' (fun k => bestW A k c c) (Finset.mem_range.2 hL)
      have h1 := Finset.le_sup' (fun j => A i j + v j) (mem_univ c)
      simp only at h1
      show A i c ≤ _
      linarith
    · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      rw [hfirst k' i c]
      apply Finset.sup'_le
      intro j _
      have h1 : bestW A k' j c ≤ v j :=
        Finset.le_sup' (fun k => bestW A k j c) (Finset.mem_range.2 (by omega))
      have h2 := Finset.le_sup' (fun j => A i j + v j) (mem_univ j)
      simp only at h2
      linarith
