-- Prove2me | solution 1 for DeltaDense.exists_card_eq_no_grid
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T17:57:45.996845+00:00
-- url     : https://prove2.me/submissions/4b4d0d45-bcf5-433e-8b9a-64c45eddd5c5

import Mathlib
import Definitions.Def_Bridges_DeltaDenseSumsetAvoidance

open DeltaDense Finset in
theorem solution {n m k : ℕ} (hmn : m ≤ n) (hk : 2 ≤ k)
    (hcond : n ^ 3 * m ^ (2 * k - 1) < n ^ (2 * k - 1)) :
    ∃ S ⊆ range n, S.card = m ∧
      ∀ t d₁ d₂ : ℕ, 0 < d₁ → 0 < d₂ → ¬ (gridWitness t d₁ d₂ k ⊆ S) := by
  classical
  obtain ⟨L, hL⟩ : ∃ L, L = 2 * k - 1 := ⟨_, rfl⟩
  rw [← hL] at hcond
  have hL3 : 3 ≤ L := by omega
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      simp [zero_pow (show L ≠ 0 by omega)] at hcond
    · exact h
  -- `(a − l)·b ≤ (b − l)·a` for `a ≤ b`
  have hkey : ∀ a b l : ℕ, a ≤ b → (a - l) * b ≤ (b - l) * a := by
    intro a b l hab
    rcases le_or_gt l a with h | h
    · have h2 : l ≤ b := h.trans hab
      zify [h, h2]
      nlinarith
    · rw [Nat.sub_eq_zero_of_le h.le, zero_mul]
      exact Nat.zero_le _
  have hdesc : ∀ l : ℕ, m.descFactorial l * n ^ l ≤ n.descFactorial l * m ^ l := by
    intro l
    induction l with
    | zero => simp
    | succ l ih =>
      rw [Nat.descFactorial_succ, Nat.descFactorial_succ, pow_succ, pow_succ]
      calc (m - l) * m.descFactorial l * (n ^ l * n)
          = (m.descFactorial l * n ^ l) * ((m - l) * n) := by ring
        _ ≤ (n.descFactorial l * m ^ l) * ((n - l) * m) :=
          Nat.mul_le_mul ih (hkey m n l hmn)
        _ = (n - l) * n.descFactorial l * (m ^ l * m) := by ring
  -- `C(n − w, m − w)·nʷ ≤ C(n, m)·mʷ`
  have hratio : ∀ w : ℕ, w ≤ m → (n - w).choose (m - w) * n ^ w ≤ n.choose m * m ^ w := by
    intro w hwm
    have hwn : w ≤ n := hwm.trans hmn
    have hc : m.choose w * n ^ w ≤ n.choose w * m ^ w := by
      have h := hdesc w
      rw [Nat.descFactorial_eq_factorial_mul_choose,
        Nat.descFactorial_eq_factorial_mul_choose] at h
      have h' : w.factorial * (m.choose w * n ^ w) ≤ w.factorial * (n.choose w * m ^ w) := by
        simpa only [mul_assoc] using h
      exact Nat.le_of_mul_le_mul_left h' (Nat.factorial_pos w)
    have hcm := Nat.choose_mul (n := n) (k := m) (s := w) hwm
    have hpos : 0 < n.choose w := Nat.choose_pos hwn
    refine Nat.le_of_mul_le_mul_left ?_ hpos
    calc n.choose w * ((n - w).choose (m - w) * n ^ w)
        = (n.choose w * (n - w).choose (m - w)) * n ^ w := by ring
      _ = (n.choose m * m.choose w) * n ^ w := by rw [hcm]
      _ = n.choose m * (m.choose w * n ^ w) := by ring
      _ ≤ n.choose m * (n.choose w * m ^ w) := Nat.mul_le_mul_left _ hc
      _ = n.choose w * (n.choose m * m ^ w) := by ring
  -- membership in an arithmetic progression
  have hmem : ∀ a d i : ℕ, i < k → a + d * i ∈ apF a d k :=
    fun a d i hi => Finset.mem_image.2 ⟨i, Finset.mem_range.2 hi, rfl⟩
  -- the L-shaped witness has at least `2k − 1` points
  have hwit : ∀ t d₁ d₂ : ℕ, 0 < d₁ → 0 < d₂ → L ≤ (gridWitness t d₁ d₂ k).card := by
    intro t d₁ d₂ h1 h2
    have hA : (apF t d₁ k).card = k := by
      unfold apF
      rw [Finset.card_image_of_injective _ (fun i j hij =>
        Nat.eq_of_mul_eq_mul_left h1 (Nat.add_left_cancel hij)), Finset.card_range]
    have hB : (apF (t + d₁ * (k - 1)) d₂ k).card = k := by
      unfold apF
      rw [Finset.card_image_of_injective _ (fun i j hij =>
        Nat.eq_of_mul_eq_mul_left h2 (Nat.add_left_cancel hij)), Finset.card_range]
    have hI : (apF t d₁ k ∩ apF (t + d₁ * (k - 1)) d₂ k).card ≤ 1 := by
      have key : ∀ z ∈ apF t d₁ k ∩ apF (t + d₁ * (k - 1)) d₂ k, z = t + d₁ * (k - 1) := by
        intro z hz
        simp only [apF, Finset.mem_inter, Finset.mem_image, Finset.mem_range] at hz
        obtain ⟨⟨i, hi, rfl⟩, j, hj, hj'⟩ := hz
        have : d₁ * i ≤ d₁ * (k - 1) := Nat.mul_le_mul_left _ (by omega)
        omega
      apply Finset.card_le_one.2
      intro x hx y hy
      rw [key x hx, key y hy]
    have hU := Finset.card_union_add_card_inter (apF t d₁ k) (apF (t + d₁ * (k - 1)) d₂ k)
    unfold gridWitness
    omega
  -- sets containing a fixed large set are rare
  have hcount : ∀ W : Finset ℕ, L ≤ W.card →
      ((powersetCard m (range n)).filter (fun S => W ⊆ S)).card * n ^ L ≤
        n.choose m * m ^ L := by
    intro W hW
    obtain ⟨cnt, hcnt⟩ : ∃ c, c = ((powersetCard m (range n)).filter (fun S => W ⊆ S)).card :=
      ⟨_, rfl⟩
    rw [← hcnt]
    by_cases hWr : W ⊆ range n
    · by_cases hwm : W.card ≤ m
      · have hle : cnt ≤ (n - W.card).choose (m - W.card) := by
          rw [hcnt]
          have h := Finset.card_le_card_of_injOn (fun S => S \ W)
            (s := (powersetCard m (range n)).filter (fun S => W ⊆ S))
            (t := powersetCard (m - W.card) (range n \ W)) ?_ ?_
          · rw [Finset.card_powersetCard, Finset.card_sdiff_of_subset hWr,
              Finset.card_range] at h
            exact h
          · intro S hS
            rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_powersetCard] at hS
            rw [Finset.mem_coe, Finset.mem_powersetCard]
            refine ⟨Finset.sdiff_subset_sdiff hS.1.1 (Finset.Subset.refl W), ?_⟩
            rw [Finset.card_sdiff_of_subset hS.2, hS.1.2]
          · intro S hS S' hS' h
            rw [Finset.mem_coe, Finset.mem_filter] at hS hS'
            have e1 := Finset.sdiff_union_of_subset hS.2
            have e2 := Finset.sdiff_union_of_subset hS'.2
            simp only at h
            rw [← e1, ← e2, h]
        have hr := hratio W.card hwm
        have hpow : m ^ W.card * n ^ L ≤ m ^ L * n ^ W.card := by
          obtain ⟨d, hd⟩ : ∃ d, W.card = L + d := ⟨W.card - L, by omega⟩
          rw [hd, pow_add, pow_add]
          calc m ^ L * m ^ d * n ^ L = m ^ L * n ^ L * m ^ d := by ring
            _ ≤ m ^ L * n ^ L * n ^ d := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hmn d)
            _ = m ^ L * (n ^ L * n ^ d) := by ring
        have hnw : 0 < n ^ W.card := pow_pos hn _
        refine Nat.le_of_mul_le_mul_right ?_ hnw
        calc cnt * n ^ L * n ^ W.card
            ≤ (n - W.card).choose (m - W.card) * n ^ L * n ^ W.card := by
              have := Nat.mul_le_mul_right (n ^ L) hle
              exact Nat.mul_le_mul_right _ this
          _ = ((n - W.card).choose (m - W.card) * n ^ W.card) * n ^ L := by ring
          _ ≤ (n.choose m * m ^ W.card) * n ^ L := Nat.mul_le_mul_right _ hr
          _ = n.choose m * (m ^ W.card * n ^ L) := by ring
          _ ≤ n.choose m * (m ^ L * n ^ W.card) := Nat.mul_le_mul_left _ hpow
          _ = n.choose m * m ^ L * n ^ W.card := by ring
      · have h0 : cnt = 0 := by
          rw [hcnt, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          intro S hS hWS
          rw [Finset.mem_powersetCard] at hS
          have := Finset.card_le_card hWS
          omega
        rw [h0, zero_mul]
        exact Nat.zero_le _
    · have h0 : cnt = 0 := by
        rw [hcnt, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro S hS hWS
        rw [Finset.mem_powersetCard] at hS
        exact hWr (hWS.trans hS.1)
      rw [h0, zero_mul]
      exact Nat.zero_le _
  -- the bad sets
  obtain ⟨bad, hbad⟩ : ∃ bad : Finset (Finset ℕ), bad = (powersetCard m (range n)).filter
      (fun S => ∃ t d₁ d₂ : ℕ, 0 < d₁ ∧ 0 < d₂ ∧ gridWitness t d₁ d₂ k ⊆ S) := ⟨_, rfl⟩
  obtain ⟨F, hF⟩ : ∃ F : ℕ × ℕ × ℕ → Finset (Finset ℕ), ∀ x, F x =
      (powersetCard m (range n)).filter
        (fun S => 0 < x.2.1 ∧ 0 < x.2.2 ∧ gridWitness x.1 x.2.1 x.2.2 k ⊆ S) := ⟨_, fun _ => rfl⟩
  have hbad_sub : bad ⊆ (range n ×ˢ range n ×ˢ range n).biUnion F := by
    intro S hS
    rw [hbad, Finset.mem_filter] at hS
    obtain ⟨hSp, t, d₁, d₂, h1, h2, hW⟩ := hS
    have hSr : S ⊆ range n := (Finset.mem_powersetCard.1 hSp).1
    have hA0 : t ∈ gridWitness t d₁ d₂ k :=
      Finset.mem_union_left _ (by simpa using hmem t d₁ 0 (by omega))
    have hA1 : t + d₁ ∈ gridWitness t d₁ d₂ k :=
      Finset.mem_union_left _ (by simpa using hmem t d₁ 1 (by omega))
    have hB1 : t + d₁ * (k - 1) + d₂ ∈ gridWitness t d₁ d₂ k :=
      Finset.mem_union_right _ (by simpa using hmem (t + d₁ * (k - 1)) d₂ 1 (by omega))
    have ht := Finset.mem_range.1 (hSr (hW hA0))
    have ht1 := Finset.mem_range.1 (hSr (hW hA1))
    have ht2 := Finset.mem_range.1 (hSr (hW hB1))
    refine Finset.mem_biUnion.2 ⟨(t, d₁, d₂), ?_, ?_⟩
    · simp only [Finset.mem_product, Finset.mem_range]
      omega
    · rw [hF, Finset.mem_filter]
      exact ⟨hSp, h1, h2, hW⟩
  have hcard_bad : bad.card * n ^ L ≤ n ^ 3 * (n.choose m * m ^ L) := by
    calc bad.card * n ^ L
        ≤ (∑ x ∈ range n ×ˢ range n ×ˢ range n, (F x).card) * n ^ L :=
          Nat.mul_le_mul_right _ ((Finset.card_le_card hbad_sub).trans Finset.card_biUnion_le)
      _ = ∑ x ∈ range n ×ˢ range n ×ˢ range n, (F x).card * n ^ L := Finset.sum_mul _ _ _
      _ ≤ ∑ x ∈ range n ×ˢ range n ×ˢ range n, n.choose m * m ^ L := by
          apply Finset.sum_le_sum
          intro x _
          by_cases hx : 0 < x.2.1 ∧ 0 < x.2.2
          · have hFx : F x = (powersetCard m (range n)).filter
                (fun S => gridWitness x.1 x.2.1 x.2.2 k ⊆ S) := by
              rw [hF]
              apply Finset.filter_congr
              intro S _
              simp [hx.1, hx.2]
            rw [hFx]
            exact hcount _ (hwit _ _ _ hx.1 hx.2)
          · have hFx : F x = ∅ := by
              rw [hF, Finset.filter_eq_empty_iff]
              intro S _ hS
              exact hx ⟨hS.1, hS.2.1⟩
            rw [hFx, Finset.card_empty, zero_mul]
            exact Nat.zero_le _
      _ = n ^ 3 * (n.choose m * m ^ L) := by
          rw [Finset.sum_const, Finset.card_product, Finset.card_product, Finset.card_range,
            smul_eq_mul]
          ring
  have hlt : bad.card < (powersetCard m (range n)).card := by
    rw [Finset.card_powersetCard, Finset.card_range]
    have hpos : 0 < n.choose m := Nat.choose_pos hmn
    by_contra hge
    have hge' : n.choose m ≤ bad.card := not_lt.1 hge
    have h1 : n.choose m * n ^ L ≤ n ^ 3 * (n.choose m * m ^ L) :=
      (Nat.mul_le_mul_right _ hge').trans hcard_bad
    have h2 : n.choose m * (n ^ 3 * m ^ L) < n.choose m * n ^ L :=
      Nat.mul_lt_mul_of_pos_left hcond hpos
    have e : n ^ 3 * (n.choose m * m ^ L) = n.choose m * (n ^ 3 * m ^ L) := by ring
    rw [e] at h1
    exact absurd (h1.trans_lt h2) (lt_irrefl _)
  obtain ⟨S, hS, hSbad⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  have hS' := Finset.mem_powersetCard.1 hS
  refine ⟨S, hS'.1, hS'.2, fun t d₁ d₂ h1 h2 hW => hSbad ?_⟩
  rw [hbad, Finset.mem_filter]
  exact ⟨hS, t, d₁, d₂, h1, h2, hW⟩
