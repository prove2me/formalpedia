-- Prove2me | solution 1 for TropicalLA.cycle_le_maxCycleMean
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T08:18:09.873508+00:00
-- url     : https://prove2.me/submissions/43cdfad5-57ee-45d3-a669-8a83588a9866

import Mathlib
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalEigenvalue
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalMatrix
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalPerronFrobenius

open Finset TropicalLA in
theorem solution {ι : Type*} [Fintype ι] [Nonempty ι] {A : Matrix ι ι ℝ} :
    ∀ (m : ℕ) (c : ℕ → ι), c m = c 0 → pathWeight A c m ≤ m * maxCycleMean A := by
  classical
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
  intro m c hc
  rcases Nat.eq_zero_or_pos m with h0 | h0
  · subst h0
    simp [pathWeight]
  · exact hmean m h0 c hc.symm
