-- Prove2me | solution 1 for TropicalLA.exists_tropEigen
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T08:29:04.271916+00:00
-- url     : https://prove2.me/submissions/9f04f9c7-ecbb-4275-8fb1-cdd622de0838

import Mathlib
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalEigenvalue
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalPerronFrobenius

open Finset TropicalLA in
theorem solution {ι : Type*} [Fintype ι] [Nonempty ι] (A : Matrix ι ι ℝ) :
    ∃ v : ι → ℝ, IsTropEigen A (maxCycleMean A) v := by
  classical
  -- the normalised case: all closed walks nonpositive, one critical cycle of weight zero
  have normalized : ∀ (A : Matrix ι ι ℝ),
      (∀ m : ℕ, 1 ≤ m → ∀ p : ℕ → ι, p 0 = p m → pathWeight A p m ≤ 0) →
      ∀ (c : ι) (L : ℕ), L < Fintype.card ι → tpow A L c c = 0 →
      ∃ v : ι → ℝ, ∀ i : ι,
        Finset.univ.sup' Finset.univ_nonempty (fun j => A i j + v j) = v i := by
    intro A H1 c L hL hc
    classical
    set N := Fintype.card ι with hN
    have hstep : ∀ m i t, tpow A (m + 1) i t
        = univ.sup' univ_nonempty (fun l => tpow A m i l + A l t) := fun _ _ _ => rfl
    -- (1) first-step decomposition of best walks
    have hfirst : ∀ k i t, tpow A (k + 1) i t
        = univ.sup' univ_nonempty (fun j => A i j + tpow A k j t) := by
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
          have h1 : ∀ j, A i j + tpow A k j l + A l t
              ≤ univ.sup' univ_nonempty (fun j => A i j + tpow A (k + 1) j t) := by
            intro j
            have h2 : tpow A k j l + A l t ≤ tpow A (k + 1) j t := by
              rw [hstep k j t]
              exact Finset.le_sup' (fun l => tpow A k j l + A l t) (mem_univ l)
            have h3 := Finset.le_sup' (fun j => A i j + tpow A (k + 1) j t) (mem_univ j)
            linarith
          have h4 : univ.sup' univ_nonempty (fun j => A i j + tpow A k j l)
              ≤ univ.sup' univ_nonempty (fun j => A i j + tpow A (k + 1) j t) - A l t :=
            Finset.sup'_le _ _ fun j _ => by linarith [h1 j]
          linarith
        · apply Finset.sup'_le
          intro j _
          rw [hstep k j t]
          have h1 : ∀ l, A i j + (tpow A k j l + A l t)
              ≤ univ.sup' univ_nonempty (fun l => tpow A (k + 1) i l + A l t) := by
            intro l
            have h2 : A i j + tpow A k j l ≤ tpow A (k + 1) i l := by
              rw [ih i l]
              exact Finset.le_sup' (fun j => A i j + tpow A k j l) (mem_univ j)
            have h3 := Finset.le_sup' (fun l => tpow A (k + 1) i l + A l t) (mem_univ l)
            linarith
          have h4 : univ.sup' univ_nonempty (fun l => tpow A k j l + A l t)
              ≤ univ.sup' univ_nonempty (fun l => tpow A (k + 1) i l + A l t) - A i j :=
            Finset.sup'_le _ _ fun l _ => by linarith [h1 l]
          linarith
    -- (2) walks: every walk is bounded by `tpow`, and `tpow` is attained
    have hbound : ∀ m (p : ℕ → ι), pathWeight A p (m + 1) ≤ tpow A m (p 0) (p (m + 1)) := by
      intro m
      induction m with
      | zero =>
        intro p
        simp [pathWeight, tpow]
      | succ m ih =>
        intro p
        have e : pathWeight A p (m + 1 + 1) = pathWeight A p (m + 1) + A (p (m + 1)) (p (m + 1 + 1)) := by
          unfold pathWeight
          rw [Finset.sum_range_succ]
        rw [e, hstep m (p 0) (p (m + 1 + 1))]
        have h1 := ih p
        have h2 := Finset.le_sup' (fun l => tpow A m (p 0) l + A l (p (m + 1 + 1)))
          (mem_univ (p (m + 1)))
        simp only at h2
        linarith
    have hattain : ∀ m i t, ∃ p : ℕ → ι, p 0 = i ∧ p (m + 1) = t ∧
        pathWeight A p (m + 1) = tpow A m i t := by
      intro m
      induction m with
      | zero =>
        intro i t
        refine ⟨fun s => if s = 0 then i else t, by simp, by simp, ?_⟩
        simp [pathWeight, tpow]
      | succ m ih =>
        intro i t
        obtain ⟨l, -, hl⟩ := Finset.exists_mem_eq_sup' univ_nonempty
          (fun l => tpow A m i l + A l t)
        obtain ⟨p, hp0, hpm, hpw⟩ := ih i l
        refine ⟨fun s => if s ≤ m + 1 then p s else t, by simp [hp0], by simp, ?_⟩
        have e1 : pathWeight A (fun s => if s ≤ m + 1 then p s else t) (m + 1) = pathWeight A p (m + 1) := by
          unfold pathWeight
          refine Finset.sum_congr rfl fun s hs => ?_
          have hs' := Finset.mem_range.1 hs
          simp only [show s ≤ m + 1 by omega, show s + 1 ≤ m + 1 by omega, if_true]
        have e2 : pathWeight A (fun s => if s ≤ m + 1 then p s else t) (m + 1 + 1)
            = pathWeight A (fun s => if s ≤ m + 1 then p s else t) (m + 1) + A l t := by
          unfold pathWeight
          rw [Finset.sum_range_succ]
          simp only [le_refl, if_true, show ¬ (m + 1 + 1 ≤ m + 1) by omega, if_false, hpm]
        rw [e2, e1, hpw, hstep m i t, hl]
    -- (3) cycle removal: `N + 1` edges never beat fewer than `N + 1` edges
    have hN0 : 0 < N := Fintype.card_pos
    have hrange : (range N).Nonempty := nonempty_range_iff.2 hN0.ne'
    set v : ι → ℝ := fun i => (range N).sup' hrange (fun k => tpow A k i c) with hv
    have hcut : ∀ i, tpow A N i c ≤ v i := by
      intro i
      obtain ⟨p, hp0, hpN, hpw⟩ := hattain N i c
      obtain ⟨x, y, hxy, hpxy⟩ := Fintype.exists_ne_map_eq_of_card_lt
        (fun s : Fin (N + 1) => p s) (by simp [hN])
      -- order the repeated positions `a < b ≤ N`
      have key : ∀ a b : ℕ, a < b → b ≤ N → p a = p b → tpow A N i c ≤ v i := by
        intro a b hab hbN hpab
        set d := b - a with hd
        set M := N - d with hM
        set q : ℕ → ι := fun s => if s ≤ a then p s else p (s + d) with hq
        have hq0 : q 0 = i := by simp [hq, hp0]
        have hqM : q (M + 1) = c := by
          simp only [hq, show ¬ (M + 1 ≤ a) by omega, if_false]
          rw [show M + 1 + d = N + 1 by omega, hpN]
        -- the removed loop has nonpositive weight
        have hloop : ∑ s ∈ range d, A (p (a + s)) (p (a + s + 1)) ≤ 0 := by
          have h1 := H1 d (by omega) (fun s => p (a + s)) (by simp [hpab, show a + d = b by omega])
          unfold pathWeight at h1
          simpa [add_assoc] using h1
        -- splitting the long walk
        have hsplit : pathWeight A p (N + 1) = pathWeight A q (M + 1)
            + ∑ s ∈ range d, A (p (a + s)) (p (a + s + 1)) := by
          unfold pathWeight
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
        have h2 : tpow A M i c ≤ v i :=
          Finset.le_sup' (fun k => tpow A k i c) (Finset.mem_range.2 (by omega))
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
      obtain ⟨k, hk, hkv⟩ := Finset.exists_mem_eq_sup' hrange (fun k => tpow A k j c)
      have hk' := Finset.mem_range.1 hk
      have h1 : A i j + tpow A k j c ≤ tpow A (k + 1) i c := by
        rw [hfirst k i c]
        exact Finset.le_sup' (fun j => A i j + tpow A k j c) (mem_univ j)
      have h2 : tpow A (k + 1) i c ≤ v i := by
        rcases Nat.lt_or_ge (k + 1) N with h | h
        · exact Finset.le_sup' (fun k => tpow A k i c) (Finset.mem_range.2 h)
        · rw [show k + 1 = N by omega]
          exact hcut i
      show A i j + v j ≤ v i
      rw [hv]
      simp only
      rw [hkv]
      linarith
    · obtain ⟨k, hk, hkv⟩ := Finset.exists_mem_eq_sup' hrange (fun k => tpow A k i c)
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
          exact Finset.le_sup' (fun k => tpow A k c c) (Finset.mem_range.2 hL)
        have h1 := Finset.le_sup' (fun j => A i j + v j) (mem_univ c)
        simp only at h1
        show A i c ≤ _
        linarith
      · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
        rw [hfirst k' i c]
        apply Finset.sup'_le
        intro j _
        have h1 : tpow A k' j c ≤ v j :=
          Finset.le_sup' (fun k => tpow A k j c) (Finset.mem_range.2 (by omega))
        have h2 := Finset.le_sup' (fun j => A i j + v j) (mem_univ j)
        simp only at h2
        linarith
  -- shifting a maximum by a constant
  have hsupc : ∀ (f : ι → ℝ) (r : ℝ),
      univ.sup' univ_nonempty (fun l => f l + r) = univ.sup' univ_nonempty f + r := by
    intro f r
    apply le_antisymm
    · apply Finset.sup'_le
      intro l _
      have := Finset.le_sup' f (mem_univ l)
      linarith
    · obtain ⟨l, -, hl⟩ := Finset.exists_mem_eq_sup' univ_nonempty f
      rw [hl]
      exact Finset.le_sup' (fun l => f l + r) (mem_univ l)
  obtain ⟨⟨k, c⟩, hkc, hmu⟩ := Finset.exists_mem_eq_sup' (cycleIndex_nonempty (ι := ι))
    (fun q : ℕ × ι => tpow A q.1 q.2 q.2 / ((q.1 : ℝ) + 1))
  have hmu' : maxCycleMean A = tpow A k c c / ((k : ℝ) + 1) := hmu
  have hkN : k < Fintype.card ι := Finset.mem_range.1 (Finset.mem_product.1 hkc).1
  have hstepA : ∀ m i t, tpow A (m + 1) i t
      = univ.sup' univ_nonempty (fun l => tpow A m i l + A l t) := fun _ _ _ => rfl
  -- every walk is bounded by `tpow`
  have hboundA : ∀ m (p : ℕ → ι), pathWeight A p (m + 1) ≤ tpow A m (p 0) (p (m + 1)) := by
    intro m
    induction m with
    | zero =>
      intro p
      simp [pathWeight, tpow]
    | succ m ih =>
      intro p
      have e : pathWeight A p (m + 1 + 1) = pathWeight A p (m + 1) + A (p (m + 1)) (p (m + 1 + 1)) := by
        unfold pathWeight
        rw [Finset.sum_range_succ]
      rw [e, hstepA m (p 0) (p (m + 1 + 1))]
      have h1 := ih p
      have h2 := Finset.le_sup' (fun l => tpow A m (p 0) l + A l (p (m + 1 + 1)))
        (mem_univ (p (m + 1)))
      simp only at h2
      linarith
  set N := Fintype.card ι with hN
  have hN0 : 0 < N := Fintype.card_pos
  set mu := maxCycleMean A with hmudef
  have hle : ∀ k' i, k' < N → tpow A k' i i / ((k' : ℝ) + 1) ≤ mu := by
    intro k' i hk
    have h := Finset.le_sup' (fun q : ℕ × ι => tpow A q.1 q.2 q.2 / ((q.1 : ℝ) + 1))
      (show (k', i) ∈ range N ×ˢ (univ : Finset ι) from
        Finset.mem_product.2 ⟨Finset.mem_range.2 hk, mem_univ i⟩)
    exact h
  -- every closed walk has mean at most `mu`
  have hmean : ∀ m, 1 ≤ m → ∀ p : ℕ → ι, p 0 = p m → pathWeight A p m ≤ m * mu := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro hm p hp
      rcases Nat.lt_or_ge N m with hNm | hmN
      · have key : ∀ a b : ℕ, a < b → b ≤ N → p a = p b → pathWeight A p m ≤ m * mu := by
          intro a b hab hbN hpab
          set d := b - a with hd
          set M := m - d with hM
          set q : ℕ → ι := fun s => if s ≤ a then p s else p (s + d) with hq
          have hloop : ∑ s ∈ range d, A (p (a + s)) (p (a + s + 1)) ≤ d * mu := by
            have h1 := ih d (by omega) (by omega) (fun s => p (a + s))
              (by simp [hpab, show a + d = b by omega])
            unfold pathWeight at h1
            simpa [add_assoc] using h1
          have hqc : pathWeight A q M ≤ M * mu := by
            apply ih M (by omega) (by omega) q
            simp only [hq, Nat.zero_le, if_true, show ¬ (M ≤ a) by omega, if_false]
            rw [show M + d = m by omega]
            exact hp
          have hsplit : pathWeight A p m = pathWeight A q M
              + ∑ s ∈ range d, A (p (a + s)) (p (a + s + 1)) := by
            unfold pathWeight
            have e1 : m = a + (d + (M - a)) := by omega
            have e2 : M = a + (M - a) := by omega
            rw [e1, Finset.sum_range_add, Finset.sum_range_add]
            conv_rhs => rw [e2, Finset.sum_range_add]
            have hA : ∑ s ∈ range a, A (q s) (q (s + 1)) = ∑ s ∈ range a, A (p s) (p (s + 1)) := by
              refine Finset.sum_congr rfl fun s hs => ?_
              have hs' := Finset.mem_range.1 hs
              simp only [hq, show s ≤ a by omega, show s + 1 ≤ a by omega, if_true]
            have hB : ∑ s ∈ range (M - a), A (q (a + s)) (q (a + s + 1))
                = ∑ s ∈ range (M - a), A (p (a + (d + s))) (p (a + (d + s) + 1)) := by
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
          have hcast : (M : ℝ) + d = m := by exact_mod_cast (show M + d = m by omega)
          rw [hsplit, ← hcast, add_mul]
          linarith
        obtain ⟨x, y, hxy, hpxy⟩ := Fintype.exists_ne_map_eq_of_card_lt
          (fun s : Fin (N + 1) => p s) (by simp [hN])
        have hx := x.isLt
        have hy := y.isLt
        rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hxy) with h | h
        · exact key x y h (by omega) hpxy
        · exact key y x h (by omega) hpxy.symm
      · obtain ⟨k', rfl⟩ : ∃ k', m = k' + 1 := ⟨m - 1, by omega⟩
        have h1 := hboundA k' p
        rw [← hp] at h1
        have h2 := hle k' (p 0) (by omega)
        have hk1 : (0 : ℝ) < (k' : ℝ) + 1 := by positivity
        rw [div_le_iff₀ hk1] at h2
        push_cast
        nlinarith
  -- normalise by `mu`
  set B : Matrix ι ι ℝ := fun i j => A i j - mu with hB
  have hwalkB : ∀ m p, pathWeight B p m = pathWeight A p m - m * mu := by
    intro m p
    unfold pathWeight
    simp only [hB, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hstepB : ∀ m i t, tpow B (m + 1) i t
      = univ.sup' univ_nonempty (fun l => tpow B m i l + B l t) := fun _ _ _ => rfl
  have hshift : ∀ m i j, tpow B m i j = tpow A m i j - ((m : ℝ) + 1) * mu := by
    intro m
    induction m with
    | zero =>
      intro i j
      simp only [tpow, hB]
      push_cast
      ring
    | succ m ih =>
      intro i j
      have e : (fun l => tpow B m i l + B l j)
          = fun l => (tpow A m i l + A l j) + (-(((m : ℝ) + 1) + 1) * mu) := by
        funext l
        rw [ih i l]
        simp only [hB]
        ring
      rw [hstepB m i j, e, hsupc, hstepA m i j]
      push_cast
      ring
  have H1B : ∀ m : ℕ, 1 ≤ m → ∀ p : ℕ → ι, p 0 = p m → pathWeight B p m ≤ 0 := by
    intro m hm p hp
    rw [hwalkB]
    linarith [hmean m hm p hp]
  have hcrit : tpow B k c c = 0 := by
    have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
    rw [hshift, hmu']
    field_simp
    ring
  obtain ⟨v, hv⟩ := normalized B H1B c k hkN hcrit
  refine ⟨v, ?_⟩
  intro i
  show univ.sup' univ_nonempty (fun j => A i j + v j) = mu + v i
  have e : (fun j => A i j + v j) = fun j => (B i j + v j) + mu := by
    funext j
    simp only [hB]
    ring
  rw [e, hsupc, hv i]
  ring
