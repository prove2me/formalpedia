-- Prove2me | solution 1 for TropicalLA.isGreatest_tropicalRoot
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T11:10:48.95155+00:00
-- url     : https://prove2.me/submissions/4e53e106-92f2-470f-80c0-68043667fba4

import Mathlib
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalCharPoly
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalPerronFrobenius

open Finset TropicalLA in
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (A : Matrix ι ι ℝ) :
    IsGreatest {x : ℝ | IsTropicalRoot A x} (maxCycleMean A) := by
  classical
  have hexists : ∃ v : ι → ℝ, IsTropEigen A (maxCycleMean A) v := by
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
  obtain ⟨v, h⟩ := hexists
  generalize maxCycleMean A = lam at h ⊢
  have hle : ∀ k : ℕ, k ≤ Fintype.card ι → charCoeff A k ≤ k * lam := by
    intro k hk
    have hne : (admPairs ι k).Nonempty := by
      obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq
        (show k ≤ (univ : Finset ι).card by simpa using hk)
      exact ⟨(s, 1), by simp [admPairs, hs]⟩
    unfold charCoeff
    rw [dif_pos hne]
    apply Finset.sup'_le
    rintro ⟨s, σ⟩ hp
    simp only [admPairs, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    obtain ⟨hcard, hmaps⟩ := hp
    dsimp only
    -- every edge is dominated by the eigen-equation
    have hedge : ∀ i, A i (σ i) ≤ lam + v i - v (σ i) := by
      intro i
      have h1 := Finset.le_sup' (fun j => A i j + v j) (mem_univ (σ i))
      have h2 : univ.sup' univ_nonempty (fun j => A i j + v j) = lam + v i := h i
      simp only at h1
      linarith
    -- `σ` permutes `s`, so the potential terms cancel
    have himage : s.image σ = s := by
      apply Finset.eq_of_subset_of_card_le
      · intro x hx
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
        exact hmaps y hy
      · simp [Finset.card_image_of_injective _ σ.injective]
    have hsum : ∑ i ∈ s, v (σ i) = ∑ i ∈ s, v i := by
      rw [← Finset.sum_image (f := v) (g := σ) (fun x _ y _ hxy => σ.injective hxy), himage]
    unfold minorWeight
    calc ∑ i ∈ s, A i (σ i) ≤ ∑ i ∈ s, (lam + v i - v (σ i)) :=
          Finset.sum_le_sum fun i _ => hedge i
      _ = k * lam := by
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hsum, Finset.sum_const, hcard,
          nsmul_eq_mul]
        ring
  have hexk : ∃ k : ℕ, 0 < k ∧ k ≤ Fintype.card ι ∧ charCoeff A k = k * lam := by
    obtain ⟨f, y, p, hp, hper, hmin, hf⟩ := h.exists_minimal_periodic_point
    -- the orbit of `y` has exactly `p` points
    have hinj : ∀ a b, a < p → b < p → f^[a] y = f^[b] y → a = b := by
      have key : ∀ a b, a < b → b < p → f^[a] y = f^[b] y → False := by
        intro a b hab hb hfab
        have e : f^[p - a] (f^[a] y) = f^[p - a] (f^[b] y) := by rw [hfab]
        rw [← Function.iterate_add_apply, ← Function.iterate_add_apply,
          show p - a + a = p by omega, hper, show p - a + b = (b - a) + p by omega,
          Function.iterate_add_apply, hper] at e
        exact hmin (b - a) (by omega) (by omega) e.symm
      intro a b ha hb hab
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · exact key a b hlt hb hab
      · exact key b a hlt ha hab.symm
    have hback : ∀ a, f^[p - 1] (f^[a + 1] y) = f^[a] y := by
      intro a
      rw [← Function.iterate_add_apply, show p - 1 + (a + 1) = a + p by omega,
        Function.iterate_add_apply, hper]
    have hinjf : ∀ a b, a < p → b < p → f (f^[a] y) = f (f^[b] y) → a = b := by
      intro a b ha hb hab
      apply hinj a b ha hb
      rw [← hback a, ← hback b, Function.iterate_succ_apply', Function.iterate_succ_apply', hab]
    set s : Finset ι := (range p).image (fun t => f^[t] y) with hs
    have hmem : ∀ x, x ∈ s ↔ ∃ t, t < p ∧ f^[t] y = x := by
      intro x
      simp [hs]
    have hcard : s.card = p := by
      rw [hs, Finset.card_image_of_injOn, Finset.card_range]
      intro a ha b hb hab
      exact hinj a b (Finset.mem_range.1 ha) (Finset.mem_range.1 hb) hab
    have hfs : ∀ x ∈ s, f x ∈ s := by
      intro x hx
      obtain ⟨t, ht, rfl⟩ := (hmem x).1 hx
      rw [hmem]
      rcases Nat.lt_or_ge (t + 1) p with h1 | h1
      · exact ⟨t + 1, h1, Function.iterate_succ_apply' f t y⟩
      · refine ⟨0, hp, ?_⟩
        rw [show p = t + 1 by omega] at hper
        rw [← Function.iterate_succ_apply' f t y, hper]
        rfl
    have hfinj : ∀ x ∈ s, ∀ x' ∈ s, f x = f x' → x = x' := by
      intro x hx x' hx' hxx
      obtain ⟨a, ha, rfl⟩ := (hmem x).1 hx
      obtain ⟨b, hb, rfl⟩ := (hmem x').1 hx'
      rw [hinjf a b ha hb hxx]
    -- the cyclic permutation of the orbit
    set g : ι → ι := fun x => if x ∈ s then f x else x with hg
    have hginj : Function.Injective g := by
      intro x x' hxx
      by_cases hx : x ∈ s <;> by_cases hx' : x' ∈ s
      · simp only [hg, hx, hx', if_true] at hxx
        exact hfinj x hx x' hx' hxx
      · simp only [hg, hx, hx', if_true, if_false] at hxx
        exact absurd (hxx ▸ hfs x hx) hx'
      · simp only [hg, hx, hx', if_true, if_false] at hxx
        exact absurd (hxx ▸ hfs x' hx') hx
      · simpa [hg, hx, hx'] using hxx
    set σ : Equiv.Perm ι := Equiv.ofBijective g (Finite.injective_iff_bijective.1 hginj) with hσ
    have hσs : ∀ x ∈ s, σ x = f x := by
      intro x hx
      simp [hσ, hg, hx]
    have hadm : (s, σ) ∈ admPairs ι p := by
      simp only [admPairs, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨hcard, fun x hx => ?_⟩
      rw [hσs x hx]
      exact hfs x hx
    -- its weight is exactly `p * lam`
    have himage : s.image σ = s := by
      apply Finset.eq_of_subset_of_card_le
      · intro x hx
        obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hx
        rw [hσs z hz]
        exact hfs z hz
      · simp [Finset.card_image_of_injective _ σ.injective]
    have hsum : ∑ x ∈ s, v (σ x) = ∑ x ∈ s, v x := by
      rw [← Finset.sum_image (f := v) (g := σ) (fun x _ z _ hxz => σ.injective hxz), himage]
    have hw : minorWeight A s σ = p * lam := by
      unfold minorWeight
      have e : ∀ x ∈ s, A x (σ x) = lam + v x - v (σ x) := by
        intro x hx
        rw [hσs x hx]
        linarith [hf x]
      rw [Finset.sum_congr rfl e, Finset.sum_sub_distrib, Finset.sum_add_distrib, hsum,
        Finset.sum_const, hcard, nsmul_eq_mul]
      ring
    have hpn : p ≤ Fintype.card ι := by
      rw [← hcard]
      exact Finset.card_le_univ s
    refine ⟨p, hp, hpn, le_antisymm (hle p hpn) ?_⟩
    unfold charCoeff
    rw [dif_pos ⟨_, hadm⟩, ← hw]
    exact Finset.le_sup' (fun q : Finset ι × Equiv.Perm ι => minorWeight A q.1 q.2) hadm
  have hc0 : charCoeff A 0 = 0 := by
    unfold charCoeff
    split_ifs with hne
    · apply le_antisymm
      · apply Finset.sup'_le
        rintro ⟨s, σ⟩ hsσ
        simp only [admPairs, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.card_eq_zero] at hsσ
        obtain ⟨rfl, -⟩ := hsσ
        simp [minorWeight]
      · refine le_trans (le_of_eq ?_) (Finset.le_sup'
          (fun q : Finset ι × Equiv.Perm ι => minorWeight A q.1 q.2)
          (show ((∅ : Finset ι), (1 : Equiv.Perm ι)) ∈ admPairs ι 0 by simp [admPairs]))
        simp [minorWeight]
    · rfl
  have hval : charPolyVal A lam = (Fintype.card ι : ℝ) * lam := by
    unfold charPolyVal
    apply le_antisymm
    · apply Finset.sup'_le
      intro k hk
      have hk' : k ≤ Fintype.card ι := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
      have := hle k hk'
      linarith
    · refine le_trans (le_of_eq ?_) (Finset.le_sup'
        (fun k => charCoeff A k + ((Fintype.card ι : ℝ) - k) * lam)
        (Finset.mem_range.2 (Nat.succ_pos _)))
      simp [hc0]
  have hroot : IsTropicalRoot A lam := by
    obtain ⟨k, hk, hkn, hkc⟩ := hexk
    refine ⟨0, k, Nat.zero_le _, hkn, by omega, ?_, ?_⟩
    · rw [hval, hc0]
      push_cast
      ring
    · rw [hval, hkc]
      ring
  refine ⟨hroot, ?_⟩
  rintro x ⟨k₁, k₂, hk₁, hk₂, hne, h₁, h₂⟩
  by_contra hx
  have hx' : lam < x := not_le.1 hx
  have h0 : charCoeff A 0 + ((Fintype.card ι : ℝ) - ((0 : ℕ) : ℝ)) * x ≤ charPolyVal A x :=
    Finset.le_sup' (fun k => charCoeff A k + ((Fintype.card ι : ℝ) - k) * x)
      (Finset.mem_range.2 (Nat.succ_pos _))
  simp only [Nat.cast_zero, sub_zero, hc0, zero_add] at h0
  have key : ∀ k, 0 < k → k ≤ Fintype.card ι →
      charCoeff A k + ((Fintype.card ι : ℝ) - k) * x = charPolyVal A x → False := by
    intro k hk hkn hkeq
    have h1 := hle k hkn
    have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
    nlinarith [mul_pos hkpos (sub_pos.2 hx')]
  rcases Nat.eq_zero_or_pos k₁ with h0' | h0'
  · exact key k₂ (by omega) hk₂ h₂
  · exact key k₁ h0' hk₁ h₁
