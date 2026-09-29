-- Prove2me | solution 1 for TropicalLA.critPotential_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T10:39:54.488365+00:00
-- url     : https://prove2.me/submissions/bd717d66-0f17-4168-9f91-0d3699846cec

import Mathlib
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalIrreducible
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalReducible

open Finset TropicalLA in
theorem solution {ι : Type*} [Fintype ι] [Nonempty ι] {A : Matrix ι ι (WithBot ℝ)} {lam : ℝ}
    (hle : AllSuppCyclesLe A lam) (hreach : ReachesCritical A lam) {c₀ : ι}
    (hc₀ : IsCriticalNode A lam c₀) {i j : ι} (hij : A i j ≠ ⊥) :
    normApprox A lam i j + critPotential A lam c₀ j ≤ critPotential A lam c₀ i := by
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
  -- (needs `hle`) short closed walks have nonpositive penalised weight
  have hshortcyc : ∀ d (p : ℕ → ι), 0 < d → d ≤ Fintype.card ι → p d = p 0 →
      pathWeight (normApprox A lam) p d ≤ 0 := by
    intro d p hd hdn hpd
    by_cases hs : IsSuppWalk A p d
    · rw [hsuppeq d p hs]
      have := hle d p hs hpd
      linarith
    · simp only [IsSuppWalk, not_forall] at hs
      obtain ⟨t, ht, hbot⟩ := hs
      have hbot' : A (p t) (p (t + 1)) = ⊥ := by
        by_contra hne
        exact hbot hne
      have := hbot_lt p d t hdn ht hbot'
      linarith
  -- every entry of a power is dominated by a power of exponent `< card ι`
  have hcut : ∀ k i x, ∃ k' < Fintype.card ι,
      tpow (normApprox A lam) k i x ≤ tpow (normApprox A lam) k' i x := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro i x
      rcases Nat.lt_or_ge k (Fintype.card ι) with hk | hk
      · exact ⟨k, hk, le_rfl⟩
      · obtain ⟨p, hp0, hpk, hpw⟩ := hattainG (normApprox A lam) k i x
        have key : ∀ a b : ℕ, a < b → b ≤ Fintype.card ι → p a = p b → ∃ k' < Fintype.card ι,
            tpow (normApprox A lam) k i x ≤ tpow (normApprox A lam) k' i x := by
          intro a b hab hbN hpab
          set d := b - a with hd
          set M := k - d with hM
          set q : ℕ → ι := fun s => if s ≤ a then p s else p (s + d) with hq
          have hloop : ∑ s ∈ range d, normApprox A lam (p (a + s)) (p (a + s + 1)) ≤ 0 := by
            have h1 := hshortcyc d (fun s => p (a + s)) (by omega) (by omega)
              (by simp [hpab, show a + d = b by omega])
            unfold pathWeight at h1
            simpa [add_assoc] using h1
          have hsplit : pathWeight (normApprox A lam) p (k + 1)
              = pathWeight (normApprox A lam) q (M + 1)
                + ∑ s ∈ range d, normApprox A lam (p (a + s)) (p (a + s + 1)) := by
            unfold pathWeight
            have e1 : k + 1 = a + (d + (M + 1 - a)) := by omega
            have e2 : M + 1 = a + (M + 1 - a) := by omega
            rw [e1, Finset.sum_range_add, Finset.sum_range_add]
            conv_rhs => rw [e2, Finset.sum_range_add]
            have hA : ∑ s ∈ range a, normApprox A lam (q s) (q (s + 1))
                = ∑ s ∈ range a, normApprox A lam (p s) (p (s + 1)) := by
              refine Finset.sum_congr rfl fun s hs => ?_
              have hs' := Finset.mem_range.1 hs
              simp only [hq, show s ≤ a by omega, show s + 1 ≤ a by omega, if_true]
            have hB : ∑ s ∈ range (M + 1 - a), normApprox A lam (q (a + s)) (q (a + s + 1))
                = ∑ s ∈ range (M + 1 - a),
                    normApprox A lam (p (a + (d + s))) (p (a + (d + s) + 1)) := by
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
          have hq0 : q 0 = i := by simp [hq, hp0]
          have hqM : q (M + 1) = x := by
            simp only [hq, show ¬ (M + 1 ≤ a) by omega, if_false]
            rw [show M + 1 + d = k + 1 by omega, hpk]
          have h1 := hboundG (normApprox A lam) M q
          rw [hq0, hqM] at h1
          obtain ⟨k', hk', hk'le⟩ := ih M (by omega) i x
          exact ⟨k', hk', by linarith⟩
        obtain ⟨y, z, hyz, hpyz⟩ := Fintype.exists_ne_map_eq_of_card_lt
          (fun s : Fin (Fintype.card ι + 1) => p s) (by simp)
        have hy := y.isLt
        have hz := z.isLt
        rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hyz) with h | h
        · exact key y z h (by omega) hpyz
        · exact key z y h (by omega) hpyz.symm
  -- (needs `hc₀`) the maximiser of a potential
  have hcp_eq : ∀ j, ∃ k y, k < Fintype.card ι ∧ IsCriticalNode A lam y ∧
      critPotential A lam c₀ j = tpow (normApprox A lam) k j y := by
    intro j
    unfold critPotential
    obtain ⟨⟨k, x⟩, hmem, heq⟩ := Finset.exists_mem_eq_sup' (cycleIndex_nonempty (ι := ι))
      (fun q : ℕ × ι => tpow (normApprox A lam) q.1 j
        (if IsCriticalNode A lam q.2 then q.2 else c₀))
    refine ⟨k, if IsCriticalNode A lam x then x else c₀,
      Finset.mem_range.1 (Finset.mem_product.1 hmem).1, ?_, heq⟩
    split_ifs with hx
    · exact hx
    · exact hc₀
  -- the potential is superharmonic along every edge
  have hle_cp : ∀ i j, normApprox A lam i j + critPotential A lam c₀ j ≤ critPotential A lam c₀ i := by
    intro i j
    obtain ⟨k, y, hk, hy, heq⟩ := hcp_eq j
    rw [heq]
    have h1 : normApprox A lam i j + tpow (normApprox A lam) k j y
        ≤ tpow (normApprox A lam) (k + 1) i y := by
      rw [hfirstG]
      exact Finset.le_sup' (fun j => normApprox A lam i j + tpow (normApprox A lam) k j y)
        (mem_univ j)
    obtain ⟨k', hk', h2⟩ := hcut (k + 1) i y
    have h3 := hcp_ge c₀ i k' y hk' hy
    linarith
  -- potentials of critical nodes are nonnegative
  have hnonneg : ∀ c, IsCriticalNode A lam c → 0 ≤ critPotential A lam c₀ c := by
    intro c hc
    have hc' := hc
    obtain ⟨m, p, hm, hp0, hpm, hps, hpw⟩ := hc
    have h0 : pathWeight (normApprox A lam) p m = 0 := by
      rw [hsuppeq m p hps, hpw]
      ring
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have h1 := hboundG (normApprox A lam) m' p
    rw [hp0, hpm, h0] at h1
    obtain ⟨k', hk', h2⟩ := hcut m' c c
    have h3 := hcp_ge c₀ c k' c hk' hc'
    linarith
  exact hle_cp i j
