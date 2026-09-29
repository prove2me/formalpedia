-- Prove2me | solution 2 for PriceOfUniversality.price_unbounded_in_parameters
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-21T01:08:22.667533+00:00
-- url     : https://prove2.me/submissions/38853b6b-1232-4cc1-842b-114463aa66d1

import Mathlib
import Definitions.Def_Novelty_BinomialConcentration
import Definitions.Def_Novelty_UniversalRedundancyCore
import Definitions.Def_Novelty_UniversalRedundancyBernoulli
import Definitions.Def_Novelty_UniversalRedundancyShtarkov
import Definitions.Def_Novelty_UniversalRedundancyPi

set_option maxHeartbeats 4000000 in
open PriceOfUniversality Finset Real in
theorem solution (C : ℝ) (n : ℕ) (hn : 32 ≤ n) :
    ∃ k : ℕ, ∀ {L : (Fin k → Msg n) → ℕ}, IsCode L →
      ∃ (j : Fin k → Fin (n + 1)) (x : Fin k → Msg n),
        C ≤ (L x : ℝ) + Real.logb 2 (kBernClass k n j x) := by
  classical
  -- ==== the five PriceOfUniversality lemmas, proved from the definitions ====
  have one_le_shtarkov : ∀ {A : Type} [Fintype A] [Nonempty A] {Θ : Type} [Fintype Θ]
      [Nonempty Θ] {p : Θ → A → ℝ}, (∀ θ, IsPMF (p θ)) → 1 ≤ shtarkov p := by
    intro A _ _ Θ _ _ p hp
    obtain ⟨θ₀⟩ := (inferInstance : Nonempty Θ)
    have h1 : ∑ a, p θ₀ a = 1 := (hp θ₀).total
    rw [shtarkov, ← h1]
    refine Finset.sum_le_sum fun a _ => ?_
    exact Finset.le_sup' (fun θ => p θ a) (Finset.mem_univ θ₀)
  have hcard : ∀ (n k : ℕ),
      ((univ : Finset (Finset (Fin n))).filter (fun s => #s = k)).card = n.choose k := by
    intro n k
    have h : (univ : Finset (Finset (Fin n))).filter (fun s => #s = k)
        = Finset.powersetCard k (univ : Finset (Fin n)) := by
      ext s; simp [Finset.mem_powersetCard, Finset.subset_univ]
    rw [h, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  have hcount : ∀ (n : ℕ) (f : ℕ → ℝ),
      ∑ s : Finset (Fin n), f (#s) = ∑ k ∈ range (n + 1), (n.choose k : ℝ) * f k := by
    intro n f
    have hmaps : ∀ s ∈ (univ : Finset (Finset (Fin n))), #s ∈ range (n + 1) := by
      intro s _
      simp only [Finset.mem_range]
      have h := Finset.card_le_univ s
      rw [Fintype.card_fin] at h
      omega
    rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun s => f (#s))]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_congr rfl (fun s hs => by
      simp only [Finset.mem_filter] at hs; rw [hs.2]), Finset.sum_const, hcard n k, nsmul_eq_mul]
  -- `binw` is the total mass of the messages of a given size
  have hbinw_eq : ∀ (n k : ℕ) (t : ℝ),
      ∑ s ∈ (univ : Finset (Msg n)).filter (fun s => #s = k), bern n t s = binw n t k := by
    intro n k t
    rw [Finset.sum_congr rfl (fun s hs => by
      simp only [Finset.mem_filter] at hs
      simp only [bern]
      rw [hs.2]), Finset.sum_const, hcard n k, nsmul_eq_mul]
    simp only [binw]
  have hbern_sum : ∀ (n : ℕ) (t : ℝ), ∑ s : Msg n, bern n t s = 1 := by
    intro n t
    have hb := add_pow t (1 - t) n
    rw [show t + (1 - t) = 1 by ring, one_pow] at hb
    have h := hcount n (fun k => t ^ k * (1 - t) ^ (n - k))
    simp only [bern]
    rw [h]
    have hre : ∑ k ∈ range (n + 1), ((n.choose k : ℝ) * (t ^ k * (1 - t) ^ (n - k)))
        = ∑ k ∈ range (n + 1), t ^ k * (1 - t) ^ (n - k) * (n.choose k : ℝ) :=
      Finset.sum_congr rfl fun k _ => by ring
    rw [hre, ← hb]
  have hgrid : ∀ (n : ℕ) (j : Fin (n + 1)),
      0 ≤ ((j : ℕ) : ℝ) / (n : ℝ) ∧ ((j : ℕ) : ℝ) / (n : ℝ) ≤ 1 := by
    intro n j
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have hj : ((j : ℕ) : ℝ) ≤ (n : ℝ) := by
        have hlt := j.isLt
        exact_mod_cast Nat.lt_succ_iff.mp hlt
      exact ⟨by positivity, by rw [div_le_one hn']; exact hj⟩
  have bernClass_isPMF : ∀ (n : ℕ) (j : Fin (n + 1)), IsPMF (bernClass n j) := by
    intro n j
    obtain ⟨h0, h1⟩ := hgrid n j
    refine ⟨fun s => ?_, ?_⟩
    · simp only [bernClass, bern]
      have h1t : (0 : ℝ) ≤ 1 - ((j : ℕ) : ℝ) / (n : ℝ) := by linarith
      positivity
    · simp only [bernClass]
      exact hbern_sum n _
  have hmaxLik_nonneg : ∀ (n : ℕ) (s : Msg n), 0 ≤ maxLik (bernClass n) s := by
    intro n s
    refine le_trans ((bernClass_isPMF n 0).nonneg s) ?_
    exact Finset.le_sup' (fun j => bernClass n j s) (Finset.mem_univ (0 : Fin (n + 1)))
  have sum_windows_le_shtarkov : ∀ (n : ℕ) (I : Finset ℕ) (K : ℕ → Finset ℕ),
      (∀ i ∈ I, K i ⊆ range (n + 1)) → (I : Set ℕ).PairwiseDisjoint K →
      ∀ (jsel : ℕ → Fin (n + 1)),
      ∑ i ∈ I, ∑ k ∈ K i, binw n ((jsel i : ℝ) / n) k ≤ shtarkov (bernClass n) := by
    intro n I K hK hdisj jsel
    set S : ℕ → Finset (Msg n) :=
      fun i => (univ : Finset (Msg n)).filter (fun s => #s ∈ K i) with hSdef
    have hwin : ∀ i ∈ I, ∑ k ∈ K i, binw n ((jsel i : ℝ) / n) k
        = ∑ s ∈ S i, bern n ((jsel i : ℝ) / n) s := by
      intro i _
      have hmaps : ∀ s ∈ S i, #s ∈ K i := by
        intro s hs
        simp only [hSdef, Finset.mem_filter] at hs
        exact hs.2
      rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun s => bern n ((jsel i : ℝ) / n) s)]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [← hbinw_eq n k ((jsel i : ℝ) / n)]
      refine Finset.sum_congr ?_ (fun _ _ => rfl)
      ext s
      have h3 : #s = k → #s ∈ K i := fun hh => by rw [hh]; exact hk
      simp only [hSdef, Finset.mem_filter, Finset.mem_univ, true_and]
      tauto
    have hmax : ∀ i, ∑ s ∈ S i, bern n ((jsel i : ℝ) / n) s
        ≤ ∑ s ∈ S i, maxLik (bernClass n) s := by
      intro i
      refine Finset.sum_le_sum fun s _ => ?_
      exact Finset.le_sup' (fun j => bernClass n j s) (Finset.mem_univ (jsel i))
    have hSdisj : (I : Set ℕ).PairwiseDisjoint S := by
      intro i hi j hj hij
      simp only [Function.onFun, Finset.disjoint_left]
      intro s hsi hsj
      simp only [hSdef, Finset.mem_filter] at hsi hsj
      have hd := hdisj hi hj hij
      simp only [Function.onFun, Finset.disjoint_left] at hd
      exact hd hsi.2 hsj.2
    calc ∑ i ∈ I, ∑ k ∈ K i, binw n ((jsel i : ℝ) / n) k
        = ∑ i ∈ I, ∑ s ∈ S i, bern n ((jsel i : ℝ) / n) s := Finset.sum_congr rfl hwin
      _ ≤ ∑ i ∈ I, ∑ s ∈ S i, maxLik (bernClass n) s :=
          Finset.sum_le_sum fun i _ => hmax i
      _ = ∑ s ∈ I.biUnion S, maxLik (bernClass n) s := (Finset.sum_biUnion hSdisj).symm
      _ ≤ ∑ s : Msg n, maxLik (bernClass n) s := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) ?_
          intro s _ _
          exact hmaxLik_nonneg n s
      _ = shtarkov (bernClass n) := rfl
  have htot : ∀ (n : ℕ) (t : ℝ), ∑ k ∈ range (n + 1), binw n t k = 1 := by
    intro n t
    have h := add_pow t (1 - t) n
    rw [show t + (1 - t) = 1 by ring, one_pow] at h
    rw [show (1:ℝ) = ∑ k ∈ range (n + 1), t ^ k * (1 - t) ^ (n - k) * (n.choose k : ℝ) from h]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [binw]
    ring
  have hchoose : ∀ (m i : ℕ), ((i : ℝ) + 1) * ((m + 1).choose (i + 1) : ℝ)
      = ((m : ℝ) + 1) * (m.choose i : ℝ) := by
    intro m i
    have h := Nat.succ_mul_choose_eq m i
    have : (((m + 1) * m.choose i : ℕ) : ℝ) = (((m + 1).choose (i + 1) * (i + 1) : ℕ) : ℝ) := by
      exact_mod_cast congrArg (fun x : ℕ => (x : ℝ)) h
    push_cast at this
    linarith [this]
  have hmean : ∀ (n : ℕ) (t : ℝ),
      ∑ k ∈ range (n + 1), (k : ℝ) * binw n t k = (n : ℝ) * t := by
    intro n t
    rcases n with _ | m
    · simp [binw]
    · rw [Finset.sum_range_succ']
      have hz : (0 : ℝ) * binw (m + 1) t 0 = 0 := by ring
      have hterm : ∀ i ∈ range (m + 1),
          ((i : ℕ) + 1 : ℝ) * binw (m + 1) t (i + 1)
            = ((m : ℝ) + 1) * t * binw m t i := by
        intro i _
        simp only [binw]
        have hsub : m + 1 - (i + 1) = m - i := by omega
        rw [hsub]
        have hc := hchoose m i
        push_cast
        linear_combination (t ^ (i + 1) * (1 - t) ^ (m - i)) * hc
      push_cast
      rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, htot m t]
      push_cast
      ring
  have hmean2 : ∀ (n : ℕ) (t : ℝ),
      ∑ k ∈ range (n + 1), ((k : ℝ) * ((k : ℝ) - 1)) * binw n t k
        = (n : ℝ) * ((n : ℝ) - 1) * t ^ 2 := by
    intro n t
    rcases n with _ | m
    · simp [binw]
    · rcases m with _ | m
      · simp [binw, Finset.sum_range_succ]
      · have hterm : ∀ j ∈ range (m + 1),
            ((((j : ℕ) + 2 : ℕ) : ℝ) * ((((j : ℕ) + 2 : ℕ) : ℝ) - 1)) * binw (m + 2) t (j + 2)
              = ((m : ℝ) + 2) * ((m : ℝ) + 1) * t ^ 2 * binw m t j := by
          intro j _
          simp only [binw]
          have hsub : m + 2 - (j + 2) = m - j := by omega
          rw [hsub]
          have h1 := hchoose (m + 1) (j + 1)
          have h2 := hchoose m j
          push_cast at h1 h2 ⊢
          linear_combination (((j : ℝ) + 1) * (t ^ (j + 2) * (1 - t) ^ (m - j))) * h1
            + (((m : ℝ) + 2) * (t ^ (j + 2) * (1 - t) ^ (m - j))) * h2
        rw [Finset.sum_range_succ', Finset.sum_range_succ', Finset.sum_congr rfl hterm,
          ← Finset.mul_sum, htot m t]
        push_cast
        ring
  have hvar : ∀ (n : ℕ) (t : ℝ),
      ∑ k ∈ range (n + 1), (((k : ℝ) - (n : ℝ) * t) ^ 2) * binw n t k
        = (n : ℝ) * t * (1 - t) := by
    intro n t
    have e : ∀ k ∈ range (n + 1), (((k : ℝ) - (n : ℝ) * t) ^ 2) * binw n t k
        = ((k : ℝ) * ((k : ℝ) - 1)) * binw n t k
          + (1 - 2 * (n : ℝ) * t) * ((k : ℝ) * binw n t k)
          + ((n : ℝ) * t) ^ 2 * binw n t k := by
      intro k _; ring
    rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, hmean2 n t, hmean n t, htot n t]
    ring
  have hnn : ∀ (n : ℕ) (t : ℝ), 0 ≤ t → t ≤ 1 → ∀ k, 0 ≤ binw n t k := by
    intro n t ht0 ht1 k
    unfold binw
    have h1t : (0:ℝ) ≤ 1 - t := by linarith
    positivity
  have binw_concentration : ∀ {n : ℕ} {t d : ℝ}, 0 ≤ t → t ≤ 1 → 0 < d →
      ∀ {K : Finset ℕ}, K ⊆ range (n + 1) →
      (∀ k ∈ range (n + 1), k ∉ K → d ^ 2 ≤ ((k : ℝ) - (n : ℝ) * t) ^ 2) →
      1 - (n : ℝ) * t * (1 - t) / d ^ 2 ≤ ∑ k ∈ K, binw n t k := by
    intro n t d ht0 ht1 hd K hK hnear
    have hd2 : (0:ℝ) < d ^ 2 := by positivity
    have hsplit : ∑ k ∈ (range (n + 1)) \ K, binw n t k + ∑ k ∈ K, binw n t k
        = ∑ k ∈ range (n + 1), binw n t k := Finset.sum_sdiff hK
    have hbad : ∑ k ∈ (range (n + 1)) \ K, binw n t k
        ≤ (n : ℝ) * t * (1 - t) / d ^ 2 := by
      have h1 : ∀ k ∈ (range (n + 1)) \ K,
          binw n t k ≤ (((k : ℝ) - (n : ℝ) * t) ^ 2 * binw n t k) / d ^ 2 := by
        intro k hk
        rw [Finset.mem_sdiff] at hk
        have hge := hnear k hk.1 hk.2
        have hb := hnn n t ht0 ht1 k
        rw [le_div_iff₀ hd2]
        nlinarith [hb, hge]
      calc ∑ k ∈ (range (n + 1)) \ K, binw n t k
          ≤ ∑ k ∈ (range (n + 1)) \ K,
              (((k : ℝ) - (n : ℝ) * t) ^ 2 * binw n t k) / d ^ 2 := Finset.sum_le_sum h1
        _ = (∑ k ∈ (range (n + 1)) \ K, ((k : ℝ) - (n : ℝ) * t) ^ 2 * binw n t k) / d ^ 2 := by
            rw [Finset.sum_div]
        _ ≤ (∑ k ∈ range (n + 1), ((k : ℝ) - (n : ℝ) * t) ^ 2 * binw n t k) / d ^ 2 := by
            have hle : (∑ k ∈ (range (n + 1)) \ K, ((k : ℝ) - (n : ℝ) * t) ^ 2 * binw n t k)
                ≤ ∑ k ∈ range (n + 1), ((k : ℝ) - (n : ℝ) * t) ^ 2 * binw n t k := by
              refine Finset.sum_le_sum_of_subset_of_nonneg
                (show (range (n + 1)) \ K ⊆ range (n + 1) from Finset.sdiff_subset) ?_
              intro i _ _
              have hb := hnn n t ht0 ht1 i
              positivity
            first
              | (rw [div_le_div_iff_of_pos_right hd2]; exact hle)
              | (rw [div_le_div_iff hd2 hd2]; nlinarith [hle, hd2])
              | exact div_le_div_of_nonneg_right hle hd2
              | exact (div_le_div_iff_right hd2).mpr hle
        _ = (n : ℝ) * t * (1 - t) / d ^ 2 := by rw [hvar]
    have htotn := htot n t
    linarith [hsplit, hbad, htotn]
  have code_regret_ge_logb_shtarkov : ∀ {A : Type} [Fintype A] [Nonempty A] {Θ : Type} [Fintype Θ] [Nonempty Θ]
      {p : Θ → A → ℝ} {L : A → ℕ}, (∀ θ, IsPMF (p θ)) → IsCode L →
      ∃ (θ : Θ) (a : A), logb 2 (shtarkov p) ≤ (L a : ℝ) + logb 2 (p θ a) := by
    intro A _ _ Θ _ _ p L hp hL
    by_contra hcon
    push_neg at hcon
    have hS1 : 1 ≤ shtarkov p := one_le_shtarkov hp
    have hS0 : (0:ℝ) < shtarkov p := by linarith
    have hl2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
    have hkey : ∀ a : A, maxLik p a < shtarkov p * ((2:ℝ)⁻¹) ^ (L a) := by
      intro a
      obtain ⟨θ, -, hθ⟩ :=
        Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := Θ)) (fun θ => p θ a)
      have hM : maxLik p a = p θ a := hθ
      have hMnn : 0 ≤ maxLik p a := by
        rw [hM]; exact (hp θ).nonneg a
      rcases eq_or_lt_of_le hMnn with h0 | hpos
      · rw [← h0]
        positivity
      · -- the maximiser makes the log inequality strict
        have hlog2 : Real.logb 2 ((2:ℝ) ^ (L a)) = (L a : ℝ) := by
          rw [Real.logb, Real.log_pow]
          field_simp
        by_contra hge
        push_neg at hge
        have h2n : (0:ℝ) < (2:ℝ) ^ (L a) := by positivity
        have hpow : ((2:ℝ)⁻¹) ^ (L a) * (2:ℝ) ^ (L a) = 1 := by
          rw [← mul_pow]; norm_num
        have hprod : shtarkov p ≤ maxLik p a * (2:ℝ) ^ (L a) := by
          have hm := mul_le_mul_of_nonneg_right hge (le_of_lt h2n)
          rwa [mul_assoc, hpow, mul_one] at hm
        have hmono := Real.logb_le_logb_of_le (by norm_num : (1:ℝ) < 2) hS0 hprod
        rw [Real.logb_mul (by linarith) (by positivity), hlog2, hM] at hmono
        linarith [hcon θ a]
    have hsum : shtarkov p < shtarkov p * kraftSum L := by
      calc shtarkov p = ∑ a, maxLik p a := rfl
        _ < ∑ a : A, shtarkov p * ((2:ℝ)⁻¹) ^ (L a) :=
            Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun a _ => hkey a)
        _ = shtarkov p * kraftSum L := by rw [kraftSum, Finset.mul_sum]
    have hk : kraftSum L ≤ 1 := hL
    nlinarith [hsum, hk, hS0]
  -- ==== end of inlined lemmas ====
  -- the square-root lower bound (its own target is still open)
  have hsqrt : Real.sqrt n / 4 ≤ shtarkov (bernClass n) := by
    have hn : 1 ≤ n := by omega
    classical
    have hn0 : 0 < n := hn
    have hone : (1 : ℝ) ≤ shtarkov (bernClass n) := one_le_shtarkov (bernClass_isPMF n)
    -- a family of `m` disjoint windows of width `2s`
    have hfam : ∀ s m : ℕ, 0 < s → 2 * m * s ≤ n + 1 →
        (m : ℝ) * (1 - (n : ℝ) / (4 * (s : ℝ) ^ 2)) ≤ shtarkov (bernClass n) := by
      intro s m hs hm
      classical
      have hwin : ∀ i : ℕ, 2 * i * s + 2 * s ≤ n + 1 →
          1 - (n : ℝ) / (4 * (s : ℝ) ^ 2)
            ≤ ∑ k ∈ Finset.Ico (2 * i * s) (2 * i * s + 2 * s),
                binw n (((2 * i * s + s : ℕ) : ℝ) / (n : ℝ)) k := by
        intro i hlast
        classical
        have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
        have hsR : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs
        set t : ℝ := ((2 * i * s + s : ℕ) : ℝ) / (n : ℝ) with htdef
        have hjle : (2 * i * s + s : ℕ) ≤ n := by omega
        have ht0 : (0 : ℝ) ≤ t := by positivity
        have ht1 : t ≤ 1 := by
          rw [htdef, div_le_one hnR]
          exact_mod_cast hjle
        have hnt : (n : ℝ) * t = ((2 * i * s + s : ℕ) : ℝ) := by
          rw [htdef]; field_simp
        have hK : Finset.Ico (2 * i * s) (2 * i * s + 2 * s) ⊆ Finset.range (n + 1) := by
          intro k hk
          rw [Finset.mem_Ico] at hk
          rw [Finset.mem_range]
          omega
        have hnear : ∀ k ∈ Finset.range (n + 1), k ∉ Finset.Ico (2 * i * s) (2 * i * s + 2 * s) →
            (s : ℝ) ^ 2 ≤ ((k : ℝ) - (n : ℝ) * t) ^ 2 := by
          intro k _ hk
          rw [Finset.mem_Ico] at hk
          push_neg at hk
          rw [hnt]
          have habs : (s : ℝ) ≤ |(k : ℝ) - ((2 * i * s + s : ℕ) : ℝ)| := by
            rcases lt_or_ge k (2 * i * s) with hlt | hge
            · have hcast : (k : ℝ) ≤ ((2 * i * s : ℕ) : ℝ) := by exact_mod_cast le_of_lt hlt
              have hneg : (k : ℝ) - ((2 * i * s + s : ℕ) : ℝ) ≤ -(s : ℝ) := by
                push_cast at hcast ⊢
                linarith
              have := neg_le_abs ((k : ℝ) - ((2 * i * s + s : ℕ) : ℝ))
              linarith
            · have hk2 : 2 * i * s + 2 * s ≤ k := hk hge
              have hcast : ((2 * i * s + 2 * s : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
              have hpos : (s : ℝ) ≤ (k : ℝ) - ((2 * i * s + s : ℕ) : ℝ) := by
                push_cast at hcast ⊢
                linarith
              exact le_trans hpos (le_abs_self _)
          nlinarith [habs, abs_nonneg ((k : ℝ) - ((2 * i * s + s : ℕ) : ℝ)),
            sq_abs ((k : ℝ) - ((2 * i * s + s : ℕ) : ℝ)), hsR]
        have hconc := binw_concentration ht0 ht1 hsR hK hnear
        have hvar : (n : ℝ) * t * (1 - t) / (s : ℝ) ^ 2 ≤ (n : ℝ) / (4 * (s : ℝ) ^ 2) := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          have hs2 : (0 : ℝ) < (s : ℝ) ^ 2 := by positivity
          nlinarith [mul_nonneg (mul_nonneg (le_of_lt hnR) (le_of_lt hs2)) (sq_nonneg (2 * t - 1))]
        linarith [hconc, hvar]
      -- the window family
      have hbound : ∀ i ∈ Finset.range m, 2 * i * s + 2 * s ≤ n + 1 := by
        intro i hi
        rw [Finset.mem_range] at hi
        have : 2 * i * s + 2 * s ≤ 2 * m * s := by nlinarith [hi, hs]
        omega
      set jsel : ℕ → Fin (n + 1) := fun i => ⟨min (2 * i * s + s) n, by omega⟩ with hjdef
      have hjval : ∀ i ∈ Finset.range m, ((jsel i : ℕ) : ℝ) = ((2 * i * s + s : ℕ) : ℝ) := by
        intro i hi
        have h := hbound i hi
        rw [hjdef]
        simp only []
        rw [min_eq_left (by omega)]
      have hKsub : ∀ i ∈ Finset.range m,
          Finset.Ico (2 * i * s) (2 * i * s + 2 * s) ⊆ Finset.range (n + 1) := by
        intro i hi k hk
        have h := hbound i hi
        rw [Finset.mem_Ico] at hk
        rw [Finset.mem_range]
        omega
      have hdisj : ((Finset.range m : Finset ℕ) : Set ℕ).PairwiseDisjoint
          (fun i => Finset.Ico (2 * i * s) (2 * i * s + 2 * s)) := by
        intro a _ b _ hab
        simp only [Function.onFun, Finset.disjoint_left]
        intro k hka hkb
        rw [Finset.mem_Ico] at hka hkb
        rcases Nat.lt_or_ge a b with h | h
        · have : 2 * a * s + 2 * s ≤ 2 * b * s := by nlinarith [h, hs]
          omega
        · have hba : b < a := by omega
          have : 2 * b * s + 2 * s ≤ 2 * a * s := by nlinarith [hba, hs]
          omega
      have hsum := sum_windows_le_shtarkov n (Finset.range m)
        (fun i => Finset.Ico (2 * i * s) (2 * i * s + 2 * s)) hKsub hdisj jsel
      have hlow : (m : ℝ) * (1 - (n : ℝ) / (4 * (s : ℝ) ^ 2))
          ≤ ∑ i ∈ Finset.range m, ∑ k ∈ Finset.Ico (2 * i * s) (2 * i * s + 2 * s),
              binw n ((jsel i : ℝ) / (n : ℝ)) k := by
        have hterm : ∀ i ∈ Finset.range m,
            1 - (n : ℝ) / (4 * (s : ℝ) ^ 2)
              ≤ ∑ k ∈ Finset.Ico (2 * i * s) (2 * i * s + 2 * s),
                  binw n ((jsel i : ℝ) / (n : ℝ)) k := by
          intro i hi
          rw [hjval i hi]
          exact hwin i (hbound i hi)
        calc (m : ℝ) * (1 - (n : ℝ) / (4 * (s : ℝ) ^ 2))
            = ∑ _i ∈ Finset.range m, (1 - (n : ℝ) / (4 * (s : ℝ) ^ 2)) := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          _ ≤ _ := Finset.sum_le_sum hterm
      linarith [hlow, hsum]
    by_cases h16 : n ≤ 16
    · -- small `n`: the trivial bound already beats √n/4
      have hs16 : Real.sqrt n ≤ 4 := by
        have h1 : Real.sqrt n ≤ Real.sqrt 16 := Real.sqrt_le_sqrt (by exact_mod_cast h16)
        have h2 : Real.sqrt 16 = 4 := by
          rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
        linarith [h1, h2.le, h2.ge]
      linarith [hone, hs16]
    · push_neg at h16
      by_cases h24 : n ≤ 24
      · -- 17 ≤ n ≤ 24: two windows of half-width 4
        have hb := hfam 4 2 (by norm_num) (show 2 * 2 * 4 ≤ n + 1 by omega)
        have hs5 : Real.sqrt n ≤ 5 := by
          have h1 : Real.sqrt n ≤ Real.sqrt 25 := Real.sqrt_le_sqrt (by exact_mod_cast (by omega : n ≤ 25))
          have h2 : Real.sqrt 25 = 5 := by
            rw [show (25 : ℝ) = 5 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
          linarith [h1, h2.le, h2.ge]
        have hnR : (n : ℝ) ≤ 24 := by exact_mod_cast h24
        push_cast at hb
        have hval : ((2 : ℝ)) * (1 - (n : ℝ) / (4 * (4 : ℝ) ^ 2)) = 2 - (n : ℝ) / 32 := by
          norm_num
          ring
        rw [hval] at hb
        linarith [hb, hs5, hnR]
      · push_neg at h24
        -- n ≥ 25: windows of half-width ⌊√n⌋
        set s : ℕ := Nat.sqrt n with hsdef
        have hs5 : 5 ≤ s := by
          rw [hsdef]
          calc 5 = Nat.sqrt 25 := by norm_num
            _ ≤ Nat.sqrt n := Nat.sqrt_le_sqrt (by omega)
        have hs0 : 0 < s := by omega
        have hsq : s ^ 2 ≤ n := by rw [hsdef]; exact Nat.sqrt_le' n
        have hlt : n < (s + 1) ^ 2 := by rw [hsdef]; exact Nat.lt_succ_sqrt' n
        set m : ℕ := (n + 1) / (2 * s) with hmdef
        have hm2s : 2 * m * s ≤ n + 1 := by
          have h := Nat.div_mul_le_self (n + 1) (2 * s)
          rw [hmdef]
          calc 2 * ((n + 1) / (2 * s)) * s = ((n + 1) / (2 * s)) * (2 * s) := by ring
            _ ≤ n + 1 := h
        have hmgt : n + 2 ≤ 2 * m * s + 2 * s := by
          have hlt2 : (n + 1) / (2 * s) < m + 1 := by rw [hmdef]; omega
          have h := (Nat.div_lt_iff_lt_mul (show 0 < 2 * s by omega)).mp hlt2
          calc n + 2 ≤ (m + 1) * (2 * s) := h
            _ = 2 * m * s + 2 * s := by ring
        have hb := hfam s m hs0 hm2s
        -- real versions
        have hsR : (5 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs5
        have hs0R : (0 : ℝ) < (s : ℝ) := by linarith
        have hsqR : ((s : ℝ)) ^ 2 ≤ (n : ℝ) := by exact_mod_cast hsq
        have hltN : n ≤ s ^ 2 + 2 * s := by
          have hexp : (s + 1) ^ 2 = s ^ 2 + 2 * s + 1 := by ring
          rw [hexp] at hlt
          omega
        have hltR : (n : ℝ) ≤ (s : ℝ) ^ 2 + 2 * (s : ℝ) := by exact_mod_cast hltN
        have hmR : ((n : ℝ) + 2 - 2 * (s : ℝ)) ≤ 2 * (m : ℝ) * (s : ℝ) := by
          have : ((n + 2 : ℕ) : ℝ) ≤ ((2 * m * s + 2 * s : ℕ) : ℝ) := by exact_mod_cast hmgt
          push_cast at this
          linarith
        -- √n ≤ n / s
        have hs_le_sqrt : (s : ℝ) ≤ Real.sqrt n := by
          have hrw : (s : ℝ) = Real.sqrt ((s : ℝ) ^ 2) := (Real.sqrt_sq hs0R.le).symm
          rw [hrw]
          exact Real.sqrt_le_sqrt hsqR
        have hmulself : Real.sqrt n * Real.sqrt n = (n : ℝ) :=
          Real.mul_self_sqrt (by positivity)
        have hsqrt : Real.sqrt n ≤ (n : ℝ) / (s : ℝ) := by
          rw [le_div_iff₀ hs0R]
          nlinarith [hs_le_sqrt, hmulself, Real.sqrt_nonneg (n : ℝ)]
        -- the polynomial inequality
        have hkey : 2 * (s : ℝ) ^ 2 * (n : ℝ)
            ≤ ((n : ℝ) + 2 - 2 * (s : ℝ)) * (4 * (s : ℝ) ^ 2 - (n : ℝ)) := by
          have hr0 : (0 : ℝ) ≤ (n : ℝ) - (s : ℝ) ^ 2 := by linarith
          have hr2 : (n : ℝ) - (s : ℝ) ^ 2 ≤ 2 * (s : ℝ) := by linarith
          have hprod : (0 : ℝ)
              ≤ ((n : ℝ) - (s : ℝ) ^ 2) * (2 * (s : ℝ) - ((n : ℝ) - (s : ℝ) ^ 2)) :=
            mul_nonneg hr0 (by linarith)
          have hfact : (s : ℝ) ^ 3 - 6 * (s : ℝ) ^ 2 + 6 * (s : ℝ) - 4
              = ((s : ℝ) - 5) * ((s : ℝ) ^ 2 - (s : ℝ) + 1) + 1 := by ring
          have hcube : (0 : ℝ) ≤ (s : ℝ) ^ 3 - 6 * (s : ℝ) ^ 2 + 6 * (s : ℝ) - 4 := by
            rw [hfact]
            have h1 : (0 : ℝ) ≤ (s : ℝ) - 5 := by linarith
            have h2 : (0 : ℝ) ≤ (s : ℝ) ^ 2 - (s : ℝ) + 1 := by
              nlinarith [mul_nonneg (le_of_lt hs0R) (show (0 : ℝ) ≤ (s : ℝ) - 1 by linarith)]
            nlinarith [mul_nonneg h1 h2]
          nlinarith [hprod, hcube, hr0, hr2, hsR, hs0R]
        have hpos : (0 : ℝ) < 4 * (s : ℝ) ^ 2 - (n : ℝ) := by nlinarith [hsR, hltR, hs0R]
        have hfin : (n : ℝ) / (4 * (s : ℝ))
            ≤ (m : ℝ) * (1 - (n : ℝ) / (4 * (s : ℝ) ^ 2)) := by
          rw [div_le_iff₀ (by positivity)]
          have hexp : (m : ℝ) * (1 - (n : ℝ) / (4 * (s : ℝ) ^ 2)) * (4 * (s : ℝ))
              = (m : ℝ) * (4 * (s : ℝ) ^ 2 - (n : ℝ)) / (s : ℝ) := by
            field_simp
          rw [hexp, le_div_iff₀ hs0R]
          nlinarith [mul_le_mul_of_nonneg_right hmR (le_of_lt hpos), hkey, hpos, hs0R]
        have hquarter : Real.sqrt n / 4 ≤ (n : ℝ) / (4 * (s : ℝ)) := by
          rw [div_le_div_iff₀ (by norm_num) (by positivity)]
          nlinarith [hsqrt, hs0R, Real.sqrt_nonneg (n : ℝ), hs_le_sqrt, hmulself]
        linarith [hquarter, hfin, hb]
  -- the product class is a PMF family
  have hpmf : ∀ (k : ℕ) (j : Fin k → Fin (n + 1)), IsPMF (kBernClass k n j) := by
    intro k j
    classical
    constructor
    · intro x
      unfold kBernClass piClass
      exact Finset.prod_nonneg fun i _ => (bernClass_isPMF n (j i)).nonneg (x i)
    · unfold kBernClass piClass
      have h : ∀ i : Fin k, ∑ a : Msg n, bernClass n (j i) a = 1 :=
        fun i => (bernClass_isPMF n (j i)).total
      calc ∑ x : Fin k → Msg n, ∏ i : Fin k, bernClass n (j i) (x i)
          = ∏ i : Fin k, ∑ a : Msg n, bernClass n (j i) a := by
            rw [Finset.prod_univ_sum]
            exact (Finset.sum_congr (by simp) fun x _ => rfl).symm
        _ = 1 := by simp [h]
  -- and its Shtarkov sum grows at least geometrically
  have hprod : ∀ k : ℕ, shtarkov (bernClass n) ^ k ≤ shtarkov (kBernClass k n) := by
    intro k
    classical
    -- the product of the coordinate maxima is attained by the tuple of argmaxes
    have hpt : ∀ x : Fin k → Msg n,
        (∏ i : Fin k, maxLik (bernClass n) (x i)) ≤ maxLik (kBernClass k n) x := by
      intro x
      have hch : ∀ i : Fin k, ∃ θ : Fin (n + 1),
          bernClass n θ (x i) = maxLik (bernClass n) (x i) := by
        intro i
        obtain ⟨θ, -, hθ⟩ := Finset.exists_mem_eq_sup' (univ_nonempty)
          (fun θ : Fin (n + 1) => bernClass n θ (x i))
        exact ⟨θ, hθ.symm⟩
      choose t ht using hch
      have hval : kBernClass k n t x = ∏ i : Fin k, maxLik (bernClass n) (x i) := by
        unfold kBernClass piClass
        exact Finset.prod_congr rfl fun i _ => ht i
      rw [← hval]
      exact Finset.le_sup' (fun θ => kBernClass k n θ x) (Finset.mem_univ t)
    calc shtarkov (bernClass n) ^ k
        = ∏ _i : Fin k, ∑ a : Msg n, maxLik (bernClass n) a := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
          rfl
      _ = ∑ x : Fin k → Msg n, ∏ i : Fin k, maxLik (bernClass n) (x i) := by
          rw [Finset.prod_univ_sum]
          exact Finset.sum_congr (by simp) fun x _ => rfl
      _ ≤ ∑ x : Fin k → Msg n, maxLik (kBernClass k n) x := Finset.sum_le_sum fun x _ => hpt x
      _ = shtarkov (kBernClass k n) := rfl
  -- `n ≥ 32` makes the one-block Shtarkov sum exceed 1
  have hnR : (32 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h525 : Real.sqrt 25 = 5 := by
    rw [show (25 : ℝ) = 5 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have h5n : (5 : ℝ) ≤ Real.sqrt n := by
    have h1 : Real.sqrt 25 ≤ Real.sqrt n := Real.sqrt_le_sqrt (by linarith)
    linarith [h1, h525.le, h525.ge]
  have hgt1 : (1 : ℝ) < shtarkov (bernClass n) := by linarith [hsqrt, h5n]
  have hlogpos : 0 < Real.logb 2 (shtarkov (bernClass n)) :=
    Real.logb_pos (by norm_num) hgt1
  obtain ⟨k, hk⟩ := exists_nat_gt (C / Real.logb 2 (shtarkov (bernClass n)))
  refine ⟨k, ?_⟩
  intro L hL
  obtain ⟨j, x, hjx⟩ := code_regret_ge_logb_shtarkov (hpmf k) hL
  refine ⟨j, x, le_trans ?_ hjx⟩
  have h1 : C ≤ (k : ℝ) * Real.logb 2 (shtarkov (bernClass n)) := by
    rw [div_lt_iff₀ hlogpos] at hk
    linarith
  have h2 : (k : ℝ) * Real.logb 2 (shtarkov (bernClass n))
      = Real.logb 2 (shtarkov (bernClass n) ^ k) := by rw [Real.logb_pow]
  have h3 : Real.logb 2 (shtarkov (bernClass n) ^ k)
      ≤ Real.logb 2 (shtarkov (kBernClass k n)) :=
    Real.logb_le_logb_of_le (by norm_num : (1:ℝ) < 2) (by positivity) (hprod k)
  linarith
