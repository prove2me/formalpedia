-- Prove2me | solution 2 for GenTuranK3t.genTuran_density_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T04:44:09.111983+00:00
-- url     : https://prove2.me/submissions/ce0f7a5e-f869-427b-9e9f-04a5ce61b5e5

import Mathlib
import Definitions.Def_Bridges_GenTuranAsymptoticBridge

open GenTuranK3t Finset Filter in
theorem solution {a b : ℕ} (ha : 3 ≤ a) (hb : 3 ≤ b)
    (G : ∀ n, SimpleGraph (Fin n)) [hG : ∀ n, DecidableRel (G n).Adj]
    (hfree : ∀ n, K3tFree (G n) (b + 1)) :
    Tendsto (fun n : ℕ => ((KabCopies (G n) a b).card : ℝ) / (n : ℝ) ^ (a + b))
      atTop (nhds 0) := by
  -- counting copies of `K_{a,b}` through a triple and its common neighbourhood
  have key : ∀ (m : ℕ) (G : SimpleGraph (Fin m)) [DecidableRel G.Adj] (t : ℕ), CNbound G t →
      (KabCopies G a b).card
        ≤ (Fintype.card (Fin m)).choose 3 * ((t - 1).choose b * (t - 1).choose (a - 3)) := by
    intro m G _ t hcn
    -- a chosen 3-subset of every set with at least three elements
    have hsel : ∀ S : Finset (Fin m), ∃ T ⊆ S, 3 ≤ S.card → T.card = 3 := by
      intro S
      by_cases h : 3 ≤ S.card
      · obtain ⟨T, hT, hTc⟩ := Finset.exists_subset_card_eq h
        exact ⟨T, hT, fun _ => hTc⟩
      · exact ⟨∅, empty_subset _, fun h' => absurd h' h⟩
    choose sel hselS hselc using hsel
    -- encode a copy `(A, B)` as `(sel A, B, A \ sel A)`
    set X := (univ.powersetCard 3).biUnion (fun T => (powersetCard b (cnbhd G T)).biUnion
        (fun B => (powersetCard (a - 3) (cnbhd G (sel B))).image (fun R => (T, B, R)))) with hX
    have hmaps : ∀ p ∈ KabCopies G a b, (sel p.1, p.2, p.1 \ sel p.1) ∈ X := by
      intro p hp
      simp only [KabCopies, mem_filter, mem_product, mem_powersetCard] at hp
      obtain ⟨⟨⟨-, hAc⟩, ⟨-, hBc⟩⟩, hdisj, hadj⟩ := hp
      have hT3 : (sel p.1).card = 3 := hselc p.1 (by omega)
      have hB3 : (sel p.2).card = 3 := hselc p.2 (by omega)
      rw [hX, mem_biUnion]
      refine ⟨sel p.1, mem_powersetCard.2 ⟨subset_univ _, hT3⟩, ?_⟩
      rw [mem_biUnion]
      refine ⟨p.2, mem_powersetCard.2 ⟨?_, hBc⟩, ?_⟩
      · intro v hv
        simp only [cnbhd, mem_filter, mem_univ, true_and]
        exact fun u hu => hadj u (hselS p.1 hu) v hv
      · rw [mem_image]
        refine ⟨p.1 \ sel p.1, mem_powersetCard.2 ⟨?_, ?_⟩, rfl⟩
        · intro w hw
          simp only [cnbhd, mem_filter, mem_univ, true_and]
          exact fun u hu => (hadj w (mem_sdiff.1 hw).1 u (hselS p.2 hu)).symm
        · rw [card_sdiff_of_subset (hselS p.1), hAc, hT3]
    have hinj : Set.InjOn (fun p : Finset (Fin m) × Finset (Fin m) => (sel p.1, p.2, p.1 \ sel p.1))
        (KabCopies G a b : Set (Finset (Fin m) × Finset (Fin m))) := by
      intro p _ p' _ h
      simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2, h3⟩ := h
      apply Prod.ext
      · rw [← union_sdiff_of_subset (hselS p.1), ← union_sdiff_of_subset (hselS p'.1), h3, h1]
      · exact h2
    calc (KabCopies G a b).card ≤ X.card :=
          card_le_card_of_injOn _ (by intro p hp; exact mem_coe.2 (hmaps p (mem_coe.1 hp))) hinj
      _ ≤ ∑ T ∈ univ.powersetCard 3, ((powersetCard b (cnbhd G T)).biUnion
            (fun B => (powersetCard (a - 3) (cnbhd G (sel B))).image (fun R => (T, B, R)))).card :=
          card_biUnion_le
      _ ≤ ∑ T ∈ univ.powersetCard 3, ((t - 1).choose b * (t - 1).choose (a - 3)) := by
          refine sum_le_sum fun T hT => ?_
          have hT3 : T.card = 3 := (mem_powersetCard.1 hT).2
          calc _ ≤ ∑ B ∈ powersetCard b (cnbhd G T),
                ((powersetCard (a - 3) (cnbhd G (sel B))).image (fun R => (T, B, R))).card :=
                card_biUnion_le
            _ ≤ ∑ B ∈ powersetCard b (cnbhd G T), (t - 1).choose (a - 3) := by
                refine sum_le_sum fun B hB => ?_
                have hBc : B.card = b := (mem_powersetCard.1 hB).2
                refine card_image_le.trans ?_
                rw [card_powersetCard]
                exact Nat.choose_le_choose _ (hcn _ (hselc B (by omega)))
            _ = (powersetCard b (cnbhd G T)).card * (t - 1).choose (a - 3) := by
                rw [sum_const, smul_eq_mul]
            _ ≤ (t - 1).choose b * (t - 1).choose (a - 3) := by
                rw [card_powersetCard]
                exact Nat.mul_le_mul_right _ (Nat.choose_le_choose _ (hcn T hT3))
      _ = (Fintype.card (Fin m)).choose 3 * ((t - 1).choose b * (t - 1).choose (a - 3)) := by
          rw [sum_const, smul_eq_mul, card_powersetCard, card_univ]
  -- `K_{3,b+1}`-freeness: every triple has at most `b` common neighbours
  have hcnb : ∀ n, CNbound (G n) (b + 1) := by
    intro n S hS
    by_contra hlt
    have hlt' : b + 1 ≤ (cnbhd (G n) S).card := by omega
    obtain ⟨B, hB, hBc⟩ := Finset.exists_subset_card_eq hlt'
    apply hfree n
    refine ⟨S, B, hS, hBc, ?_, ?_⟩
    · rw [Finset.disjoint_right]
      intro w hwB hwS
      have hw := hB hwB
      simp only [cnbhd, mem_filter, mem_univ, true_and] at hw
      exact (G n).irrefl (hw w hwS)
    · intro u hu v hv
      have hv' := hB hv
      simp only [cnbhd, mem_filter, mem_univ, true_and] at hv'
      exact hv' u hu
  -- so the count is `O(n³)`, against `n^(a+b)` with `a + b ≥ 6`
  have hbound : ∀ n : ℕ, 1 ≤ n →
      ((KabCopies (G n) a b).card : ℝ) / (n : ℝ) ^ (a + b) ≤ (b.choose (a - 3) : ℝ) / n := by
    intro n hn
    have h1 := key n (G n) (b + 1) (hcnb n)
    rw [Fintype.card_fin, Nat.add_sub_cancel, Nat.choose_self, one_mul] at h1
    have h2 : (n.choose 3 : ℝ) ≤ (n : ℝ) ^ 3 := by
      have h5 := Nat.choose_le_pow_div (α := ℝ) 3 n
      have h6 : (n : ℝ) ^ 3 / ((3 : ℕ).factorial : ℝ) ≤ (n : ℝ) ^ 3 :=
        div_le_self (by positivity) (by norm_num [Nat.factorial])
      exact h5.trans h6
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    rw [div_le_div_iff₀ (by positivity) hnpos]
    have h3 : ((KabCopies (G n) a b).card : ℝ) ≤ (n : ℝ) ^ 3 * (b.choose (a - 3) : ℝ) := by
      calc ((KabCopies (G n) a b).card : ℝ) ≤ ((n.choose 3 * b.choose (a - 3) : ℕ) : ℝ) := by
            exact_mod_cast h1
        _ = (n.choose 3 : ℝ) * (b.choose (a - 3) : ℝ) := by push_cast; ring
        _ ≤ (n : ℝ) ^ 3 * (b.choose (a - 3) : ℝ) :=
            mul_le_mul_of_nonneg_right h2 (by positivity)
    have h4 : (n : ℝ) ^ 4 ≤ (n : ℝ) ^ (a + b) :=
      pow_le_pow_right₀ (by exact_mod_cast hn) (by omega)
    calc ((KabCopies (G n) a b).card : ℝ) * n
        ≤ (n : ℝ) ^ 3 * (b.choose (a - 3) : ℝ) * n := mul_le_mul_of_nonneg_right h3 hnpos.le
      _ = (b.choose (a - 3) : ℝ) * (n : ℝ) ^ 4 := by ring
      _ ≤ (b.choose (a - 3) : ℝ) * (n : ℝ) ^ (a + b) :=
          mul_le_mul_of_nonneg_left h4 (by positivity)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (tendsto_const_div_atTop_nhds_zero_nat (b.choose (a - 3) : ℝ)) ?_ ?_
  · exact Eventually.of_forall fun n => by positivity
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact hbound n hn
