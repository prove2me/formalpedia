-- Prove2me | solution 1 for TropicalLA.exists_tropEigenBot_of_stronglyConnected
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T11:17:16.919479+00:00
-- url     : https://prove2.me/submissions/299c0149-59da-4c7e-b70a-dfa781fea8e5

import Mathlib
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalIrreducible
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalPerronFrobenius
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalReducible

open Finset TropicalLA in
theorem solution {ι : Type*} [Fintype ι] [Nonempty ι] {A : Matrix ι ι (WithBot ℝ)}
    (hSC : StronglyConnected A) :
    ∃ (lam : ℝ) (v : ι → ℝ), IsTropEigenBot A lam v ∧
      entryMin A ≤ lam ∧ lam ≤ entryMax A := by
  classical
  -- sufficiency of the two conditions (proved inline)
  have h4bd : ∀ lam : ℝ, AllSuppCyclesLe A lam → ReachesCritical A lam →
      ∃ v : ι → ℝ, IsTropEigenBot A lam v := by
    intro lam hle hreach
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
    obtain ⟨i0⟩ := ‹Nonempty ι›
    obtain ⟨m0, p0, -, -, -, hc₀⟩ := hreach i0
    set c₀ := p0 m0 with hc₀def
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
    -- a tight edge out of every vertex
    have htight : ∀ i, ∃ j, A i j ≠ ⊥ ∧
        normApprox A lam i j + critPotential A lam c₀ j = critPotential A lam c₀ i := by
      intro i
      obtain ⟨k, y, hk, hy, heq⟩ := hcp_eq i
      have hlow := hneg c₀ i
      rcases Nat.eq_zero_or_pos k with hk0 | hk0
      · subst hk0
        have heq' : critPotential A lam c₀ i = normApprox A lam i y := heq
        refine ⟨y, ?_, ?_⟩
        · intro hbot
          have hv : normApprox A lam i y = -penaltyN A lam := by
            unfold normApprox
            rw [if_pos hbot]
          rw [heq', hv] at hlow
          unfold penaltyN at hlow
          linarith
        · have h1 := hle_cp i y
          have h2 := hnonneg y hy
          linarith
      · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
        obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_sup' univ_nonempty
          (fun j => normApprox A lam i j + tpow (normApprox A lam) k' j y)
        have heq' : critPotential A lam c₀ i
            = normApprox A lam i j + tpow (normApprox A lam) k' j y := by
          rw [heq, hfirstG, hj]
        have h2 := hcp_ge c₀ j k' y (by omega) hy
        have h1 := hle_cp i j
        refine ⟨j, ?_, by linarith⟩
        intro hbot
        have hv : normApprox A lam i j = -penaltyN A lam := by
          unfold normApprox
          rw [if_pos hbot]
        have h4 := htop k' j y
        have hk1 : ((k' : ℝ) + 1) ≤ Fintype.card ι := by
          have : k' + 1 ≤ Fintype.card ι := by omega
          exact_mod_cast this
        have h5 := mul_le_mul_of_nonneg_right hk1 (by linarith : (0 : ℝ) ≤ spreadAbs A lam)
        rw [heq', hv] at hlow
        unfold penaltyN at hlow
        linarith
    have hcoe : ∀ x : WithBot ℝ, x ≠ ⊥ → x = ((x.unbotD 0 : ℝ) : WithBot ℝ) := by
      intro x hx
      induction x using WithBot.recBotCoe with
      | bot => exact absurd rfl hx
      | coe a => simp
    have hfin : ∀ i j, A i j ≠ ⊥ → normApprox A lam i j = finPart A i j - lam := by
      intro i j hne
      unfold normApprox
      rw [if_neg hne]
    refine ⟨fun j => critPotential A lam c₀ j, ?_⟩
    intro i
    show univ.sup (fun j => A i j + ((critPotential A lam c₀ j : ℝ) : WithBot ℝ))
      = ((lam + critPotential A lam c₀ i : ℝ) : WithBot ℝ)
    apply le_antisymm
    · apply Finset.sup_le
      intro j _
      by_cases hbot : A i j = ⊥
      · rw [hbot, WithBot.bot_add]
        exact bot_le
      · rw [hcoe _ hbot, ← WithBot.coe_add, WithBot.coe_le_coe]
        have h1 := hle_cp i j
        rw [hfin i j hbot] at h1
        show finPart A i j + critPotential A lam c₀ j ≤ lam + critPotential A lam c₀ i
        linarith
    · obtain ⟨j, hne, hj⟩ := htight i
      rw [hfin i j hne] at hj
      have e : A i j + ((critPotential A lam c₀ j : ℝ) : WithBot ℝ)
          = ((lam + critPotential A lam c₀ i : ℝ) : WithBot ℝ) := by
        rw [hcoe _ hne, ← WithBot.coe_add, WithBot.coe_inj]
        show finPart A i j + critPotential A lam c₀ j = lam + critPotential A lam c₀ i
        linarith
      rw [← e]
      exact Finset.le_sup (f := fun j => A i j + ((critPotential A lam c₀ j : ℝ) : WithBot ℝ))
        (mem_univ j)
  -- closed walks of a finite matrix have mean at most its maximal cycle mean
  have hcycG : ∀ (A : Matrix ι ι ℝ) (m : ℕ) (c : ℕ → ι), c m = c 0 →
      pathWeight A c m ≤ m * maxCycleMean A := by
    intro A
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
  have hstepG : ∀ (M : Matrix ι ι ℝ) m i t, tpow M (m + 1) i t
      = univ.sup' univ_nonempty (fun l => tpow M m i l + M l t) := fun _ _ _ _ => rfl
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
  -- support paths from transitive closure
  have htrans : ∀ i j, Relation.TransGen (Supp A) i j → ∃ (m : ℕ) (p : ℕ → ι), 0 < m ∧
      p 0 = i ∧ p m = j ∧ IsSuppWalk A p m := by
    intro i j hij
    induction hij with
    | single hab =>
      rename_i b
      refine ⟨1, fun s => if s = 0 then i else b, by omega, by simp, by simp, ?_⟩
      intro t ht
      have : t = 0 := by omega
      subst this
      simpa using hab
    | tail hib hbc ih =>
      rename_i b c
      obtain ⟨m, p, hm, hp0, hpm, hps⟩ := ih
      refine ⟨m + 1, fun s => if s ≤ m then p s else c, by omega, by simp [hp0], by simp, ?_⟩
      intro t ht
      by_cases htm : t < m
      · simp only [show t ≤ m by omega, show t + 1 ≤ m by omega, if_true]
        exact hps t htm
      · have : t = m := by omega
        subst this
        simp only [le_refl, if_true, show ¬ (t + 1 ≤ t) by omega, if_false, hpm]
        exact hbc
  -- the perturbed finite matrix
  set B : Matrix ι ι ℝ := approx A with hBdef
  have hn0 : (0 : ℝ) ≤ (Fintype.card ι : ℝ) := Nat.cast_nonneg _
  have hfin_lo : ∀ i j, entryMin A ≤ finPart A i j := by
    intro i j
    unfold entryMin
    exact Finset.inf'_le (fun q : ι × ι => finPart A q.1 q.2) (mem_univ (i, j))
  have hfin_hi : ∀ i j, finPart A i j ≤ entryMax A := by
    intro i j
    unfold entryMax
    exact Finset.le_sup' (fun q : ι × ι => finPart A q.1 q.2) (mem_univ (i, j))
  have hMnMx : entryMin A ≤ entryMax A := by
    obtain ⟨i0⟩ := ‹Nonempty ι›
    exact le_trans (hfin_lo i0 i0) (hfin_hi i0 i0)
  have hBsupp : ∀ i j, A i j ≠ ⊥ → B i j = finPart A i j := by
    intro i j hne
    obtain ⟨a, ha⟩ := WithBot.ne_bot_iff_exists.1 hne
    simp [hBdef, approx, finPart, ← ha]
  have hBbot : ∀ i j, A i j = ⊥ → B i j = -penalty A := by
    intro i j h
    simp [hBdef, approx, h]
  have hBle : ∀ i j, B i j ≤ entryMax A := by
    intro i j
    by_cases h : A i j = ⊥
    · rw [hBbot i j h]
      unfold penalty spreadBound
      have := mul_nonneg hn0 (sub_nonneg.2 hMnMx)
      linarith
    · rw [hBsupp i j h]
      exact hfin_hi i j
  -- a walk through a `⊥` edge has mean below `entryMin`
  have hbotwalk : ∀ (p : ℕ → ι) (L t : ℕ), L ≤ Fintype.card ι → t < L →
      A (p t) (p (t + 1)) = ⊥ → pathWeight B p L < (L : ℝ) * entryMin A := by
    intro p L t hL ht hbot
    have hsplit := Finset.add_sum_erase (range L) (fun s => B (p s) (p (s + 1)))
      (Finset.mem_range.2 ht)
    have hrest : ∑ s ∈ (range L).erase t, B (p s) (p (s + 1)) ≤ ((L : ℝ) - 1) * entryMax A := by
      have h := Finset.sum_le_card_nsmul ((range L).erase t) (fun s => B (p s) (p (s + 1)))
        (entryMax A) (fun s _ => hBle _ _)
      rw [Finset.card_erase_of_mem (Finset.mem_range.2 ht), Finset.card_range, nsmul_eq_mul] at h
      have hm1 : ((L - 1 : ℕ) : ℝ) = (L : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega)]
        simp
      rw [hm1] at h
      exact h
    have hL' : (L : ℝ) ≤ Fintype.card ι := by exact_mod_cast hL
    have hprod := mul_nonneg (by linarith : (0 : ℝ) ≤ (Fintype.card ι : ℝ) - L + 1)
      (sub_nonneg.2 hMnMx)
    unfold pathWeight
    rw [← hsplit]
    beta_reduce
    rw [hBbot _ _ hbot]
    unfold penalty spreadBound
    nlinarith
  have hsuppw : ∀ m (p : ℕ → ι), IsSuppWalk A p m →
      pathWeight (finPart A) p m = pathWeight B p m := by
    intro m p hp
    unfold pathWeight
    exact Finset.sum_congr rfl fun s hs => (hBsupp _ _ (hp s (Finset.mem_range.1 hs))).symm
  -- the maximising cycle of `B`
  obtain ⟨⟨k, c⟩, hkc, hmu⟩ := Finset.exists_mem_eq_sup' (cycleIndex_nonempty (ι := ι))
    (fun q : ℕ × ι => tpow B q.1 q.2 q.2 / ((q.1 : ℝ) + 1))
  have hmu' : maxCycleMean B = tpow B k c c / ((k : ℝ) + 1) := hmu
  have hk : k < Fintype.card ι := Finset.mem_range.1 (Finset.mem_product.1 hkc).1
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hmuk : maxCycleMean B * ((k : ℝ) + 1) = tpow B k c c := by
    rw [hmu']
    field_simp
  obtain ⟨p, hp0, hpk, hpw⟩ := hattainG B k c c
  -- some support cycle has mean at least `entryMin`
  have hMn_le : entryMin A ≤ maxCycleMean B := by
    obtain ⟨i0⟩ := ‹Nonempty ι›
    obtain ⟨m, q, hm, hq0, hqm, hqs⟩ := htrans i0 i0 (hSC i0 i0)
    obtain ⟨m', q', hm', hm'n, hq'0, hq'm, hq's⟩ := hshort m hm q hqs
    have hq'w : ((m' : ℕ) : ℝ) * entryMin A ≤ pathWeight B q' m' := by
      have h := Finset.card_nsmul_le_sum (range m') (fun s => B (q' s) (q' (s + 1))) (entryMin A)
        (fun s hs => by
          show entryMin A ≤ B (q' s) (q' (s + 1))
          rw [hBsupp _ _ (hq's s (Finset.mem_range.1 hs))]
          exact hfin_lo _ _)
      rw [Finset.card_range, nsmul_eq_mul] at h
      exact h
    obtain ⟨m'', rfl⟩ : ∃ m'', m' = m'' + 1 := ⟨m' - 1, by omega⟩
    have hq'b := hboundG B m'' q'
    rw [hq'0, hq'm, hq0, hqm] at hq'b
    have hle1 : tpow B m'' i0 i0 / ((m'' : ℝ) + 1) ≤ maxCycleMean B := by
      have h := Finset.le_sup' (fun q : ℕ × ι => tpow B q.1 q.2 q.2 / ((q.1 : ℝ) + 1))
        (show (m'', i0) ∈ range (Fintype.card ι) ×ˢ (univ : Finset ι) from
          Finset.mem_product.2 ⟨Finset.mem_range.2 (by omega), mem_univ i0⟩)
      exact h
    have h2 : entryMin A ≤ tpow B m'' i0 i0 / ((m'' : ℝ) + 1) := by
      rw [le_div_iff₀ (by positivity)]
      push_cast at hq'w
      linarith
    linarith
  -- the maximising cycle uses only support edges
  have hps : IsSuppWalk A p (k + 1) := by
    by_contra hns
    simp only [IsSuppWalk, not_forall] at hns
    obtain ⟨t, ht, hbot⟩ := hns
    have hbot' : A (p t) (p (t + 1)) = ⊥ := by
      by_contra hne
      exact hbot hne
    have h1 := hbotwalk p (k + 1) t (by omega) ht hbot'
    rw [hpw] at h1
    push_cast at h1
    nlinarith
  set mu := maxCycleMean B with hmudef
  have hcrit : IsCriticalNode A mu c := by
    refine ⟨k + 1, p, by omega, hp0, hpk, hps, ?_⟩
    rw [hsuppw _ _ hps, hpw, ← hmuk]
    push_cast
    ring
  have hmu_le : mu ≤ entryMax A := by
    have h := Finset.sum_le_card_nsmul (range (k + 1)) (fun s => finPart A (p s) (p (s + 1)))
      (entryMax A) (fun s _ => hfin_hi _ _)
    rw [Finset.card_range, nsmul_eq_mul] at h
    have e : ∑ s ∈ range (k + 1), finPart A (p s) (p (s + 1)) = mu * ((k : ℝ) + 1) := by
      have := hsuppw _ _ hps
      unfold pathWeight at this
      rw [this, ← pathWeight, hpw, hmuk]
    rw [e] at h
    push_cast at h
    nlinarith
  have hle : AllSuppCyclesLe A mu := by
    intro m q hq hqc
    rw [hsuppw m q hq]
    exact hcycG B m q hqc
  have hreach : ReachesCritical A mu := by
    intro i
    obtain ⟨m, q, hm, hq0, hqm, hqs⟩ := htrans i c (hSC i c)
    exact ⟨m, q, hm, hq0, hqs, by rw [hqm]; exact hcrit⟩
  obtain ⟨v, hv⟩ := h4bd mu hle hreach
  exact ⟨mu, v, hv, hMn_le, hmu_le⟩
