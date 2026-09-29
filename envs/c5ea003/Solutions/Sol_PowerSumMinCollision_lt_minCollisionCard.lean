-- Prove2me | solution 1 for PowerSumMinCollision.lt_minCollisionCard
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-21T01:59:36.340478+00:00
-- url     : https://prove2.me/submissions/38d0de59-0ca3-4572-86d7-b6e91d6b381b

import Mathlib
import Definitions.Def_Probability_PowerSumSharpness
import Definitions.Def_Probability_PowerSumMinimalCollision

open Finset Polynomial PowerSumSharpness PowerSumMinCollision in
theorem solution {N K : ℕ} (hK : K < N) : K < minCollisionCard N K := by
  classical
  have hN : 1 ≤ N := by omega
  have hconstr : (∀ x ∈ evenMultiset N, x ≤ N) ∧ (∀ x ∈ oddMultiset N, x ≤ N) ∧
      (∀ k < N, ((evenMultiset N).map (fun x => x ^ k)).sum
        = ((oddMultiset N).map (fun x => x ^ k)).sum) ∧
      evenMultiset N ≠ oddMultiset N ∧
      Multiset.card (evenMultiset N) = 2 ^ (N - 1) := by
    classical
    -- generic bookkeeping for a finite sum of multisets
    have hmapsum : ∀ (g : ℕ → Multiset ℕ) (f : ℕ → ℕ) (m : ℕ),
        ((∑ i ∈ range m, g i).map f).sum = ∑ i ∈ range m, ((g i).map f).sum := by
      intro g f m
      induction m with
      | zero => simp
      | succ m ih => rw [Finset.sum_range_succ, Finset.sum_range_succ, ← ih,
          Multiset.map_add, Multiset.sum_add]
    have hcardsum : ∀ (g : ℕ → Multiset ℕ) (m : ℕ),
        Multiset.card (∑ i ∈ range m, g i) = ∑ i ∈ range m, Multiset.card (g i) := by
      intro g m
      induction m with
      | zero => simp
      | succ m ih => rw [Finset.sum_range_succ, Finset.sum_range_succ, ← ih, Multiset.card_add]
    have hmemsum : ∀ (g : ℕ → Multiset ℕ) (m : ℕ) (x : ℕ),
        x ∈ (∑ i ∈ range m, g i) → ∃ i ∈ range m, x ∈ g i := by
      intro g m
      induction m with
      | zero => intro x hx; simp at hx
      | succ m ih =>
        intro x hx
        rw [Finset.sum_range_succ, Multiset.mem_add] at hx
        rcases hx with hx | hx
        · obtain ⟨i, hi, hxi⟩ := ih x hx
          exact ⟨i, mem_range.2 (Nat.lt_succ_of_lt (mem_range.1 hi)), hxi⟩
        · exact ⟨m, mem_range.2 (Nat.lt_succ_self m), hx⟩
    -- the alternating binomial identity, from Mathlib's forward differences
    have halt : ∀ j, j < N →
        ∑ i ∈ range (N + 1), ((-1 : ℝ) ^ i * (N.choose i)) * (i : ℝ) ^ j = 0 := by
      intro j hj
      have hshift := fwdDiff_iter_eq_sum_shift (h := (1 : ℝ)) (f := fun r : ℝ => r ^ j)
        (n := N) (y := 0)
      have hz : (fwdDiff (1 : ℝ))^[N] (fun r : ℝ => r ^ j) = 0 :=
        fwdDiff_iter_pow_eq_zero_of_lt hj
      have hterm : ∀ k ∈ range (N + 1),
          ((-1 : ℤ) ^ (N - k) * (N.choose k : ℤ)) • ((0 : ℝ) + k • (1 : ℝ)) ^ j
            = (-1 : ℝ) ^ N * (((-1 : ℝ) ^ k * (N.choose k : ℝ)) * (k : ℝ) ^ j) := by
        intro k hk
        have hkN : k ≤ N := Nat.lt_succ_iff.1 (mem_range.1 hk)
        have h0 : (0 : ℝ) + k • (1 : ℝ) = (k : ℝ) := by simp
        have hsign : (-1 : ℝ) ^ N * (-1 : ℝ) ^ k = (-1 : ℝ) ^ (N - k) := by
          have hNk : N + k = (N - k) + 2 * k := by omega
          rw [← pow_add, hNk, pow_add, pow_mul]
          simp
        rw [h0, zsmul_eq_mul]
        push_cast
        rw [← hsign]
        ring
      rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, hz] at hshift
      simp only [Pi.zero_apply] at hshift
      have hne : (-1 : ℝ) ^ N ≠ 0 := pow_ne_zero _ (by norm_num)
      exact (mul_eq_zero.1 hshift.symm).resolve_left hne
    -- the even and odd halves as ordinary sums
    have hevenmap : ∀ f : ℕ → ℕ, ((evenMultiset N).map f).sum
        = ∑ i ∈ range (N + 1), if Even i then N.choose i * f i else 0 := by
      intro f
      rw [evenMultiset, hmapsum]
      refine Finset.sum_congr rfl ?_
      intro i _
      by_cases hi : Even i <;> simp [hi, Multiset.map_replicate, Multiset.sum_replicate]
    have hoddmap : ∀ f : ℕ → ℕ, ((oddMultiset N).map f).sum
        = ∑ i ∈ range (N + 1), if Even i then 0 else N.choose i * f i := by
      intro f
      rw [oddMultiset, hmapsum]
      refine Finset.sum_congr rfl ?_
      intro i _
      by_cases hi : Even i <;> simp [hi, Multiset.map_replicate, Multiset.sum_replicate]
    -- equality of the two halves against any power, in ℕ
    have hhalves : ∀ k, k < N →
        (∑ i ∈ range (N + 1), if Even i then N.choose i * i ^ k else 0)
          = ∑ i ∈ range (N + 1), if Even i then 0 else N.choose i * i ^ k := by
      intro k hk
      have hcast : ((∑ i ∈ range (N + 1), if Even i then N.choose i * i ^ k else 0 : ℕ) : ℝ)
          = ((∑ i ∈ range (N + 1), if Even i then 0 else N.choose i * i ^ k : ℕ) : ℝ) := by
        push_cast
        have hsplit : (∑ i ∈ range (N + 1), if Even i then ((N.choose i : ℝ) * (i : ℝ) ^ k) else 0)
            - (∑ i ∈ range (N + 1), if Even i then 0 else ((N.choose i : ℝ) * (i : ℝ) ^ k))
            = ∑ i ∈ range (N + 1), ((-1 : ℝ) ^ i * (N.choose i)) * (i : ℝ) ^ k := by
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl ?_
          intro i _
          by_cases hi : Even i
          · rw [if_pos hi, if_pos hi, hi.neg_one_pow]
            ring
          · rw [if_neg hi, if_neg hi, (Nat.not_even_iff_odd.1 hi).neg_one_pow]
            ring
        have := halt k hk
        rw [this] at hsplit
        linarith [hsplit]
      exact_mod_cast hcast
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro x hx
      obtain ⟨i, hi, hxi⟩ := hmemsum _ _ x (by rw [evenMultiset] at hx; exact hx)
      by_cases hev : Even i
      · rw [if_pos hev] at hxi
        have hxeq : x = i := Multiset.eq_of_mem_replicate hxi
        have hilt := mem_range.1 hi
        omega
      · rw [if_neg hev] at hxi
        simp at hxi
    · intro x hx
      obtain ⟨i, hi, hxi⟩ := hmemsum _ _ x (by rw [oddMultiset] at hx; exact hx)
      by_cases hev : Even i
      · rw [if_pos hev] at hxi
        simp at hxi
      · rw [if_neg hev] at hxi
        have : x = i := Multiset.eq_of_mem_replicate hxi
        have := mem_range.1 hi
        omega
    · intro k hk
      rw [hevenmap, hoddmap]
      exact hhalves k hk
    · intro hcon
      have h0even : (0 : ℕ) ∈ evenMultiset N := by
        rw [evenMultiset, Finset.sum_range_succ']
        refine Multiset.mem_add.2 (Or.inr ?_)
        simp
      have h0odd : (0 : ℕ) ∈ oddMultiset N := by rw [← hcon]; exact h0even
      obtain ⟨i, hi, hxi⟩ := hmemsum _ _ 0 (by rw [oddMultiset] at h0odd; exact h0odd)
      by_cases hev : Even i
      · rw [if_pos hev] at hxi
        simp at hxi
      · rw [if_neg hev] at hxi
        have : (0 : ℕ) = i := Multiset.eq_of_mem_replicate hxi
        exact hev (this ▸ (⟨0, rfl⟩ : Even 0))
    · have hcard : Multiset.card (evenMultiset N)
          = ∑ i ∈ range (N + 1), if Even i then N.choose i else 0 := by
        rw [evenMultiset, hcardsum]
        refine Finset.sum_congr rfl ?_
        intro i _
        by_cases hi : Even i <;> simp [hi]
      have hcardodd : Multiset.card (oddMultiset N)
          = ∑ i ∈ range (N + 1), if Even i then 0 else N.choose i := by
        rw [oddMultiset, hcardsum]
        refine Finset.sum_congr rfl ?_
        intro i _
        by_cases hi : Even i <;> simp [hi]
      have htot : (∑ i ∈ range (N + 1), if Even i then N.choose i else 0)
          + (∑ i ∈ range (N + 1), if Even i then 0 else N.choose i) = 2 ^ N := by
        rw [← Finset.sum_add_distrib, ← Nat.sum_range_choose N]
        refine Finset.sum_congr rfl ?_
        intro i _
        by_cases hi : Even i <;> simp [hi]
      have heq := hhalves 0 (by omega)
      simp only [pow_zero, mul_one] at heq
      have h2 : 2 ^ N = 2 * 2 ^ (N - 1) := by
        conv_lhs => rw [show N = (N - 1) + 1 by omega]
        rw [pow_succ]
        ring
      rw [hcard]
      omega
  obtain ⟨he1, he2, he3, he4, he5⟩ := hconstr
  have hcol : IsCollision N K (evenMultiset N) (oddMultiset N) :=
    ⟨he1, he2, fun k hk => he3 k (by omega), he4⟩
  have hnonempty : (collisionSizes N K).Nonempty :=
    ⟨_, ⟨evenMultiset N, oddMultiset N, hcol, he5⟩⟩
  -- size-based Newton over the reals
  have newtonReal : ∀ S T : Multiset ℝ, Multiset.card S = Multiset.card T →
      (∀ m : ℕ, 1 ≤ m → m ≤ Multiset.card S →
        (S.map (fun x => x ^ m)).sum = (T.map (fun x => x ^ m)).sum) → S = T := by
    intro S T hcard h
    -- Newton's identity for an arbitrary real multiset (via its `toList`)
    have newton : ∀ (U : Multiset ℝ) (k : ℕ),
        (k : ℝ) * (U.esymm k)
          = (-1) ^ (k + 1) * ∑ a ∈ {a ∈ Finset.antidiagonal k | a.1 < k},
              (-1) ^ a.1 * (U.esymm a.1) * ((U.map (fun x => x ^ a.2)).sum) := by
      intro U k
      have key : ∀ l : List ℝ,
          (k : ℝ) * ((l : Multiset ℝ).esymm k)
            = (-1) ^ (k + 1) * ∑ a ∈ {a ∈ Finset.antidiagonal k | a.1 < k},
                (-1) ^ a.1 * ((l : Multiset ℝ).esymm a.1)
                  * (((l : Multiset ℝ).map (fun x => x ^ a.2)).sum) := by
        intro l
        have huniv : (Finset.univ.val.map l.get : Multiset ℝ) = (l : Multiset ℝ) := by
          rw [Fin.univ_val_map, List.ofFn_get]
        have hps : ∀ m : ℕ, MvPolynomial.aeval l.get (MvPolynomial.psum (Fin l.length) ℝ m)
            = (((l : Multiset ℝ)).map (fun x => x ^ m)).sum := by
          intro m
          rw [MvPolynomial.psum, map_sum]
          simp only [map_pow, MvPolynomial.aeval_X]
          rw [← huniv, Multiset.map_map]
          rfl
        have hes : ∀ m : ℕ, MvPolynomial.aeval l.get (MvPolynomial.esymm (Fin l.length) ℝ m)
            = ((l : Multiset ℝ)).esymm m := by
          intro m
          rw [MvPolynomial.aeval_esymm_eq_multiset_esymm, huniv]
        have hmul := congrArg (MvPolynomial.aeval l.get)
          (MvPolynomial.mul_esymm_eq_sum (Fin l.length) ℝ k)
        simp only [map_mul, map_natCast, map_pow, map_neg, map_one, map_sum, hes, hps] at hmul
        exact hmul
      have := key U.toList
      rwa [Multiset.coe_toList] at this
    -- all elementary symmetric functions up to the common size agree
    have hesq : ∀ k : ℕ, k ≤ Multiset.card S → S.esymm k = T.esymm k := by
      intro k
      induction k using Nat.strong_induction_on with
      | _ k ih =>
        intro hk
        rcases Nat.eq_zero_or_pos k with rfl | hkpos
        · have h0 : ∀ U : Multiset ℝ, U.esymm 0 = 1 := by
            intro U
            simp [Multiset.esymm, Multiset.powersetCard_zero_left]
          rw [h0, h0]
        · have hS := newton S k
          have hT := newton T k
          have hsum : ∑ a ∈ {a ∈ Finset.antidiagonal k | a.1 < k},
                (-1 : ℝ) ^ a.1 * (S.esymm a.1) * ((S.map (fun x => x ^ a.2)).sum)
              = ∑ a ∈ {a ∈ Finset.antidiagonal k | a.1 < k},
                (-1 : ℝ) ^ a.1 * (T.esymm a.1) * ((T.map (fun x => x ^ a.2)).sum) := by
            refine Finset.sum_congr rfl ?_
            intro a ha
            simp only [Finset.mem_filter, Finset.mem_antidiagonal] at ha
            obtain ⟨hab, halt⟩ := ha
            rw [ih a.1 halt (by omega), h a.2 (by omega) (by omega)]
          rw [hsum] at hS
          have hkne : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
          exact mul_left_cancel₀ hkne (hS.trans hT.symm)
    -- Vieta: the monic polynomials with these root multisets coincide
    have hmapneg : ∀ U : Multiset ℝ,
        ((U.map Neg.neg).map fun r => Polynomial.X + Polynomial.C r)
          = U.map (fun a => Polynomial.X - Polynomial.C a) := by
      intro U
      rw [Multiset.map_map]
      refine Multiset.map_congr rfl ?_
      intro a _
      simp [Function.comp, sub_eq_add_neg]
    have hpoly : (S.map (fun a => Polynomial.X - Polynomial.C a)).prod
        = (T.map (fun a => Polynomial.X - Polynomial.C a)).prod := by
      rw [← hmapneg S, ← hmapneg T,
        Multiset.prod_X_add_C_eq_sum_esymm, Multiset.prod_X_add_C_eq_sum_esymm,
        Multiset.card_map, Multiset.card_map, ← hcard]
      refine Finset.sum_congr rfl ?_
      intro j hj
      rw [Multiset.esymm_neg, Multiset.esymm_neg,
        hesq j (by simpa using Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))]
    calc S = (S.map (fun a => Polynomial.X - Polynomial.C a)).prod.roots :=
          (Polynomial.roots_multiset_prod_X_sub_C S).symm
      _ = (T.map (fun a => Polynomial.X - Polynomial.C a)).prod.roots := by rw [hpoly]
      _ = T := Polynomial.roots_multiset_prod_X_sub_C T

  -- transfer to multisets of naturals
  have hcs : ∀ v : Multiset ℕ, ((v.sum : ℕ) : ℝ) = (v.map (fun x : ℕ => (x : ℝ))).sum := by
    intro v
    induction v using Multiset.induction with
    | empty => simp
    | cons a v ih => simp [ih]
  have hcastsum : ∀ (u : Multiset ℕ) (m : ℕ),
      (((u.map (fun x => x ^ m)).sum : ℕ) : ℝ)
        = (((u.map (fun x : ℕ => (x : ℝ))).map (fun x => x ^ m)).sum) := by
    intro u m
    rw [hcs, Multiset.map_map, Multiset.map_map]
    refine congrArg Multiset.sum (Multiset.map_congr rfl ?_)
    intro a _
    simp [Function.comp]
  have newtonNat : ∀ s t : Multiset ℕ, Multiset.card s = Multiset.card t →
      (∀ m : ℕ, 1 ≤ m → m ≤ Multiset.card s →
        (s.map (fun x => x ^ m)).sum = (t.map (fun x => x ^ m)).sum) → s = t := by
    intro s t hc hagree
    refine Multiset.map_injective (f := fun x : ℕ => (x : ℝ)) Nat.cast_injective ?_
    refine newtonReal _ _ (by simpa using hc) ?_
    intro m hm1 hm2
    rw [← hcastsum s m, ← hcastsum t m]
    exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) (hagree m hm1 (by simpa using hm2))
  -- every collision is strictly larger than K
  have hlow : ∀ n ∈ collisionSizes N K, K < n := by
    rintro n ⟨s, t, ⟨hs, ht, hagree, hsne⟩, rfl⟩
    by_contra hcon
    push_neg at hcon
    refine hsne (newtonNat s t ?_ ?_)
    · have h0 := hagree 0 (Nat.zero_le K)
      simpa using h0
    · intro m hm1 hm2
      exact hagree m (by omega)
  exact hlow _ (Nat.sInf_mem hnonempty)
