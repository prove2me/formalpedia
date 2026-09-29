-- Prove2me | solution 1 for TropicalLA.neg_le_critPotential
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T10:35:14.733105+00:00
-- url     : https://prove2.me/submissions/9e9cc323-13a8-4ba1-8c99-e4816077469a

import Mathlib
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalIrreducible
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalReducible

open Finset TropicalLA in
theorem solution {ι : Type*} [Fintype ι] [Nonempty ι] {A : Matrix ι ι (WithBot ℝ)} {lam : ℝ}
    (hle : AllSuppCyclesLe A lam) (hreach : ReachesCritical A lam) (c₀ j : ι) :
    -((Fintype.card ι : ℝ) * spreadAbs A lam) ≤ critPotential A lam c₀ j := by
  classical
  have hS1 : 1 ≤ spreadAbs A lam := by
    unfold spreadAbs
    have := abs_nonneg (entryMax A)
    have := abs_nonneg (entryMin A)
    have := abs_nonneg lam
    linarith
  have hn0 : (0 : ℝ) ≤ (Fintype.card ι : ℝ) := Nat.cast_nonneg _
  have hnS : 0 ≤ (Fintype.card ι : ℝ) * spreadAbs A lam := mul_nonneg hn0 (by linarith)
  have hpen : 0 ≤ 2 * (Fintype.card ι : ℝ) * spreadAbs A lam :=
    mul_nonneg (mul_nonneg (by norm_num) hn0) (by linarith)
  have hstepG : ∀ (M : Matrix ι ι ℝ) m i t, tpow M (m + 1) i t
      = univ.sup' univ_nonempty (fun l => tpow M m i l + M l t) := fun _ _ _ _ => rfl
  have hfirstG : ∀ (M : Matrix ι ι ℝ) k i t, tpow M (k + 1) i t
      = univ.sup' univ_nonempty (fun j => M i j + tpow M k j t) := by
    intro M k
    induction k with
    | zero =>
      intro i t
      rfl
    | succ k ih =>
      intro i t
      rw [hstepG M (k + 1) i t]
      apply le_antisymm
      · apply Finset.sup'_le
        intro l _
        rw [ih i l]
        have h1 : ∀ j, M i j + tpow M k j l + M l t
            ≤ univ.sup' univ_nonempty (fun j => M i j + tpow M (k + 1) j t) := by
          intro j
          have h2 : tpow M k j l + M l t ≤ tpow M (k + 1) j t := by
            rw [hstepG M k j t]
            exact Finset.le_sup' (fun l => tpow M k j l + M l t) (mem_univ l)
          have h3 := Finset.le_sup' (fun j => M i j + tpow M (k + 1) j t) (mem_univ j)
          linarith
        have h4 : univ.sup' univ_nonempty (fun j => M i j + tpow M k j l)
            ≤ univ.sup' univ_nonempty (fun j => M i j + tpow M (k + 1) j t) - M l t :=
          Finset.sup'_le _ _ fun j _ => by linarith [h1 j]
        linarith
      · apply Finset.sup'_le
        intro j _
        rw [hstepG M k j t]
        have h1 : ∀ l, M i j + (tpow M k j l + M l t)
            ≤ univ.sup' univ_nonempty (fun l => tpow M (k + 1) i l + M l t) := by
          intro l
          have h2 : M i j + tpow M k j l ≤ tpow M (k + 1) i l := by
            rw [ih i l]
            exact Finset.le_sup' (fun j => M i j + tpow M k j l) (mem_univ j)
          have h3 := Finset.le_sup' (fun l => tpow M (k + 1) i l + M l t) (mem_univ l)
          linarith
        have h4 : univ.sup' univ_nonempty (fun l => tpow M k j l + M l t)
            ≤ univ.sup' univ_nonempty (fun l => tpow M (k + 1) i l + M l t) - M i j :=
          Finset.sup'_le _ _ fun l _ => by linarith [h1 l]
        linarith
  have hboundG : ∀ (M : Matrix ι ι ℝ) m (p : ℕ → ι),
      pathWeight M p (m + 1) ≤ tpow M m (p 0) (p (m + 1)) := by
    intro M m
    induction m with
    | zero =>
      intro p
      simp [pathWeight, tpow]
    | succ m ih =>
      intro p
      have e : pathWeight M p (m + 1 + 1)
          = pathWeight M p (m + 1) + M (p (m + 1)) (p (m + 1 + 1)) := by
        unfold pathWeight
        rw [Finset.sum_range_succ]
      rw [e, hstepG M m (p 0) (p (m + 1 + 1))]
      have h1 := ih p
      have h2 := Finset.le_sup' (fun l => tpow M m (p 0) l + M l (p (m + 1 + 1)))
        (mem_univ (p (m + 1)))
      simp only at h2
      linarith
  have hattainG : ∀ (M : Matrix ι ι ℝ) m i t, ∃ p : ℕ → ι, p 0 = i ∧ p (m + 1) = t ∧
      pathWeight M p (m + 1) = tpow M m i t := by
    intro M m
    induction m with
    | zero =>
      intro i t
      refine ⟨fun s => if s = 0 then i else t, by simp, by simp, ?_⟩
      simp [pathWeight, tpow]
    | succ m ih =>
      intro i t
      obtain ⟨l, -, hl⟩ := Finset.exists_mem_eq_sup' univ_nonempty
        (fun l => tpow M m i l + M l t)
      obtain ⟨p, hp0, hpm, hpw⟩ := ih i l
      refine ⟨fun s => if s ≤ m + 1 then p s else t, by simp [hp0], by simp, ?_⟩
      have e1 : pathWeight M (fun s => if s ≤ m + 1 then p s else t) (m + 1)
          = pathWeight M p (m + 1) := by
        unfold pathWeight
        refine Finset.sum_congr rfl fun s hs => ?_
        have hs' := Finset.mem_range.1 hs
        simp only [show s ≤ m + 1 by omega, show s + 1 ≤ m + 1 by omega, if_true]
      have e2 : pathWeight M (fun s => if s ≤ m + 1 then p s else t) (m + 1 + 1)
          = pathWeight M (fun s => if s ≤ m + 1 then p s else t) (m + 1) + M l t := by
        unfold pathWeight
        rw [Finset.sum_range_succ]
        simp only [le_refl, if_true, show ¬ (m + 1 + 1 ≤ m + 1) by omega, if_false, hpm]
      rw [e2, e1, hpw, hstepG M m i t, hl]
  -- entries of the penalised matrix
  have hedge_hi : ∀ i j, normApprox A lam i j ≤ spreadAbs A lam := by
    intro i j
    unfold normApprox
    split_ifs with h
    · unfold penaltyN
      linarith
    · have h1 : finPart A i j ≤ entryMax A := by
        unfold entryMax
        exact Finset.le_sup' (fun q : ι × ι => finPart A q.1 q.2) (mem_univ (i, j))
      have h2 := le_abs_self (entryMax A)
      have h3 : -lam ≤ |lam| := by
        rw [← abs_neg]
        exact le_abs_self _
      have h4 := abs_nonneg (entryMin A)
      have h5 := abs_nonneg lam
      unfold spreadAbs
      linarith
  have hedge_lo : ∀ i j, A i j ≠ ⊥ → -spreadAbs A lam ≤ normApprox A lam i j := by
    intro i j hne
    unfold normApprox
    rw [if_neg hne]
    have h1 : entryMin A ≤ finPart A i j := by
      unfold entryMin
      exact Finset.inf'_le (fun q : ι × ι => finPart A q.1 q.2) (mem_univ (i, j))
    have h2 := neg_abs_le (entryMin A)
    have h3 := le_abs_self lam
    have h4 := abs_nonneg (entryMax A)
    have h5 := abs_nonneg lam
    unfold spreadAbs
    linarith
  have hsuppeq : ∀ m (p : ℕ → ι), IsSuppWalk A p m →
      pathWeight (normApprox A lam) p m = pathWeight (finPart A) p m - m * lam := by
    intro m p hp
    unfold pathWeight
    rw [show (m : ℝ) * lam = ∑ s ∈ range m, lam by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul], ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun s hs => ?_
    unfold normApprox
    rw [if_neg (hp s (Finset.mem_range.1 hs))]
  have hbot_lt : ∀ (p : ℕ → ι) (m t : ℕ), m ≤ Fintype.card ι → t < m →
      A (p t) (p (t + 1)) = ⊥ →
      pathWeight (normApprox A lam) p m < -((Fintype.card ι : ℝ) * spreadAbs A lam) := by
    intro p m t hmn ht hbot
    have hbotv : normApprox A lam (p t) (p (t + 1)) = -penaltyN A lam := by
      unfold normApprox
      rw [if_pos hbot]
    have hsplit := Finset.add_sum_erase (range m) (fun s => normApprox A lam (p s) (p (s + 1)))
      (Finset.mem_range.2 ht)
    have hrest : ∑ s ∈ (range m).erase t, normApprox A lam (p s) (p (s + 1))
        ≤ ((m : ℝ) - 1) * spreadAbs A lam := by
      have h := Finset.sum_le_card_nsmul ((range m).erase t)
        (fun s => normApprox A lam (p s) (p (s + 1))) (spreadAbs A lam) (fun s _ => hedge_hi _ _)
      rw [Finset.card_erase_of_mem (Finset.mem_range.2 ht), Finset.card_range, nsmul_eq_mul] at h
      have hm1 : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega)]
        simp
      rw [hm1] at h
      exact h
    have hmn' : (m : ℝ) ≤ Fintype.card ι := by exact_mod_cast hmn
    have hmS := mul_le_mul_of_nonneg_right hmn' (by linarith : (0 : ℝ) ≤ spreadAbs A lam)
    unfold pathWeight
    rw [← hsplit]
    beta_reduce
    rw [hbotv]
    unfold penaltyN
    linarith
  have htop : ∀ m a b, tpow (normApprox A lam) m a b ≤ ((m : ℝ) + 1) * spreadAbs A lam := by
    intro m
    induction m with
    | zero =>
      intro a b
      have := hedge_hi a b
      simp only [tpow]
      push_cast
      linarith
    | succ m ih =>
      intro a b
      rw [hstepG]
      apply Finset.sup'_le
      intro l _
      have h1 := ih a l
      have h2 := hedge_hi l b
      push_cast
      linarith
  -- critical potentials dominate short walks into critical nodes
  have hcp_ge : ∀ c₀ j k x, k < Fintype.card ι → IsCriticalNode A lam x →
      tpow (normApprox A lam) k j x ≤ critPotential A lam c₀ j := by
    intro c₀ j k x hk hx
    unfold critPotential
    refine le_trans ?_ (Finset.le_sup' _
      (show (k, x) ∈ range (Fintype.card ι) ×ˢ (univ : Finset ι) from
        Finset.mem_product.2 ⟨Finset.mem_range.2 hk, mem_univ x⟩))
    simp only [if_pos hx, le_refl]
  -- (needs `hreach`) potentials are bounded below
  have hshort : ∀ (m : ℕ), 0 < m → ∀ p : ℕ → ι, IsSuppWalk A p m →
      ∃ (m' : ℕ) (q : ℕ → ι), 0 < m' ∧ m' ≤ Fintype.card ι ∧ q 0 = p 0 ∧ q m' = p m ∧
        IsSuppWalk A q m' := by
    classical
    set N := Fintype.card ι with hN
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro hm p hp
      rcases Nat.lt_or_ge N m with hNm | hmN
      · have key : ∀ a b : ℕ, a < b → b ≤ N → p a = p b → ∃ (m' : ℕ) (q : ℕ → ι), 0 < m' ∧
            m' ≤ N ∧ q 0 = p 0 ∧ q m' = p m ∧ IsSuppWalk A q m' := by
          intro a b hab hbN hpab
          set d := b - a with hd
          set M := m - d with hM
          set q : ℕ → ι := fun s => if s ≤ a then p s else p (s + d) with hq
          have hqs : IsSuppWalk A q M := by
            intro t ht
            rcases lt_trichotomy t a with h | h | h
            · have := hp t (by omega)
              simp only [hq, show t ≤ a by omega, show t + 1 ≤ a by omega, if_true]
              exact this
            · have := hp b (by omega)
              simp only [hq, show t ≤ a by omega, show ¬ (t + 1 ≤ a) by omega, if_true, if_false]
              rw [show t = a by omega, hpab, show a + 1 + d = b + 1 by omega]
              exact this
            · have := hp (t + d) (by omega)
              simp only [hq, show ¬ (t ≤ a) by omega, show ¬ (t + 1 ≤ a) by omega, if_false]
              rw [show t + 1 + d = t + d + 1 by omega]
              exact this
          obtain ⟨m', q', hm', hm'N, hq'0, hq'm, hq'w⟩ := ih M (by omega) (by omega) q hqs
          refine ⟨m', q', hm', hm'N, ?_, ?_, hq'w⟩
          · rw [hq'0]
            simp only [hq, Nat.zero_le, if_true]
          · rw [hq'm]
            simp only [hq, show ¬ (M ≤ a) by omega, if_false]
            rw [show M + d = m by omega]
        obtain ⟨x, y, hxy, hpxy⟩ := Fintype.exists_ne_map_eq_of_card_lt
          (fun s : Fin (N + 1) => p s) (by simp [hN])
        have hx := x.isLt
        have hy := y.isLt
        rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hxy) with h | h
        · exact key x y h (by omega) hpxy
        · exact key y x h (by omega) hpxy.symm
      · exact ⟨m, p, hm, hmN, rfl, rfl, hp⟩
  have hneg : ∀ c₀ j, -((Fintype.card ι : ℝ) * spreadAbs A lam) ≤ critPotential A lam c₀ j := by
    intro c₀ j
    obtain ⟨m, p, hm, hp0, hps, hpc⟩ := hreach j
    obtain ⟨m', q, hm', hm'n, hq0, hqm, hqs⟩ := hshort m hm p hps
    have hw : ∑ s ∈ range m', (-spreadAbs A lam) ≤ pathWeight (normApprox A lam) q m' := by
      unfold pathWeight
      exact Finset.sum_le_sum fun s hs => hedge_lo _ _ (hqs s (Finset.mem_range.1 hs))
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hw
    obtain ⟨k, rfl⟩ : ∃ k, m' = k + 1 := ⟨m' - 1, by omega⟩
    have h1 := hboundG (normApprox A lam) k q
    rw [hq0, hqm, hp0] at h1
    have h2 := hcp_ge c₀ j k (p m) (by omega) hpc
    have hk : ((k + 1 : ℕ) : ℝ) ≤ Fintype.card ι := by exact_mod_cast hm'n
    have h3 := mul_le_mul_of_nonneg_right hk (by linarith : (0 : ℝ) ≤ spreadAbs A lam)
    linarith
  exact hneg c₀ j
