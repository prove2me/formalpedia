-- Prove2me | solution 2 for RomanDomination.gammaDR_K_eq
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T15:07:28.492469+00:00
-- url     : https://prove2.me/submissions/2a45b8f1-5835-42d9-8218-9e37c6e5f658

import Mathlib
import Definitions.Def_Geometry_RomanDomination_ConvexBipartite
import Definitions.Def_Geometry_RomanDomination_DoubleRoman
import Definitions.Def_Geometry_RomanDomination_Variants
open RomanDomination Finset in
theorem solution {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    gammaDR (K m n) = if min m n = 1 then 3 else if min m n = 2 then 4 else 6 := by
  classical
  -- `γ_dR = c` as soon as `c` is attained and is a lower bound
  have key : ∀ c, (∃ f, IsDRDF (K m n) f ∧ weight f = c) →
      (∀ f, IsDRDF (K m n) f → c ≤ weight f) → gammaDR (K m n) = c := by
    rintro c ⟨f, hf, hw⟩ hlow
    unfold gammaDR
    apply le_antisymm
    · exact Nat.sInf_le ⟨f, hf, hw⟩
    · exact le_csInf ⟨c, f, hf, hw⟩ (by rintro w ⟨g, hg, rfl⟩; exact hlow g hg)
  -- LOWER BOUNDS
  -- `3 ≤ weight`: look at the adjacent pair `inl 0`, `inr 0`
  have three_le : ∀ f : Fin m ⊕ Fin n → ℕ, IsDRDF (K m n) f → 3 ≤ weight f := by
    intro f hf
    have single : ∀ x, f x ≤ weight f := fun x =>
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ x)
    have pair : ∀ x y, x ≠ y → f x + f y ≤ weight f := by
      intro x y hxy
      rw [← Finset.sum_pair hxy]
      exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    -- a `0`-vertex forces weight `≥ 3`
    have zero_case : ∀ x, f x = 0 → 3 ≤ weight f := by
      intro x hx
      rcases hf.2.1 x hx with ⟨u, -, hu⟩ | ⟨u, w, huw, -, -, hu2, hw2⟩
      · have := single u; omega
      · have := pair u w huw; omega
    set a : Fin m ⊕ Fin n := Sum.inl ⟨0, by omega⟩
    set b : Fin m ⊕ Fin n := Sum.inr ⟨0, by omega⟩
    have hab : a ≠ b := Sum.inl_ne_inr
    rcases Nat.lt_or_ge (f a) 2 with ha | ha
    · rcases Nat.lt_succ_iff.mp ha |>.lt_or_eq with ha0 | ha1
      · exact zero_case a (by omega)
      · obtain ⟨u, hadj, hu⟩ := hf.2.2 a ha1
        have := pair a u ((K m n).ne_of_adj hadj)
        omega
    · by_cases hb : f b = 0
      · exact zero_case b hb
      · have := pair a b hab
        omega
  have four_le : ∀ f : Fin m ⊕ Fin n → ℕ, 2 ≤ m → 2 ≤ n → IsDRDF (K m n) f → 4 ≤ weight f := by
    intro f hm hn hf
    have hw : weight f = ∑ i, f (Sum.inl i) + ∑ j, f (Sum.inr j) := Fintype.sum_sum_type f
    have singleL : ∀ i, f (Sum.inl i) ≤ ∑ i, f (Sum.inl i) := fun i =>
      Finset.single_le_sum (f := fun i => f (Sum.inl i)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    have singleR : ∀ j, f (Sum.inr j) ≤ ∑ j, f (Sum.inr j) := fun j =>
      Finset.single_le_sum (f := fun j => f (Sum.inr j)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    have pairL : ∀ a b : Fin m, a ≠ b → f (Sum.inl a) + f (Sum.inl b) ≤ ∑ i, f (Sum.inl i) := by
      intro a b hab
      rw [← Finset.sum_pair (f := fun i => f (Sum.inl i)) hab]
      exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    by_cases hA0 : ∃ i, f (Sum.inl i) = 0
    · obtain ⟨i, hi⟩ := hA0
      rcases hf.2.1 (Sum.inl i) hi with ⟨u, hadj, hu⟩ | ⟨u, w, huw, hu, hw', hu2, hw2⟩
      · cases u with
        | inl i' => simp at hadj
        | inr j =>
          have hB3 := singleR j
          by_cases hA1 : 1 ≤ ∑ i, f (Sum.inl i)
          · omega
          · -- all left labels vanish, so every right label is at least `2`
            have hle : ∀ i, f (Sum.inl i) = 0 := fun i => by have := singleL i; omega
            have hright : ∀ j, 2 ≤ f (Sum.inr j) := by
              intro j
              by_contra hlt
              push Not at hlt
              rcases Nat.lt_succ_iff.mp hlt |>.lt_or_eq with h0 | h1
              · have h0' : f (Sum.inr j) = 0 := by omega
                rcases hf.2.1 (Sum.inr j) h0' with ⟨u, hadj, hu⟩ | ⟨u, w, -, hu, -, hu2, -⟩
                · cases u with
                  | inl i => rw [hle i] at hu; omega
                  | inr j' => simp at hadj
                · cases u with
                  | inl i => rw [hle i] at hu2; omega
                  | inr j' => simp at hu
              · obtain ⟨u, hadj, hu⟩ := hf.2.2 (Sum.inr j) h1
                cases u with
                | inl i => rw [hle i] at hu; omega
                | inr j' => simp at hadj
            have hB : 2 * n ≤ ∑ j, f (Sum.inr j) := by
              calc 2 * n = ∑ _j : Fin n, 2 := by simp [mul_comm]
                _ ≤ ∑ j, f (Sum.inr j) := Finset.sum_le_sum fun j _ => hright j
            omega
      · cases u with
        | inl i' => simp at hu
        | inr j₁ =>
          cases w with
          | inl i' => simp at hw'
          | inr j₂ =>
            have hne : j₁ ≠ j₂ := fun h => huw (by rw [h])
            have : f (Sum.inr j₁) + f (Sum.inr j₂) ≤ ∑ j, f (Sum.inr j) := by
              rw [← Finset.sum_pair (f := fun j => f (Sum.inr j)) hne]
              exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
            omega
    · push Not at hA0
      have hA : m ≤ ∑ i, f (Sum.inl i) := by
        calc m = ∑ _i : Fin m, 1 := by simp
          _ ≤ ∑ i, f (Sum.inl i) := Finset.sum_le_sum fun i _ => Nat.one_le_iff_ne_zero.mpr (hA0 i)
      by_cases hB0 : ∃ j, f (Sum.inr j) = 0
      · obtain ⟨j, hj⟩ := hB0
        rcases hf.2.1 (Sum.inr j) hj with ⟨u, hadj, hu⟩ | ⟨u, w, huw, hu, hw', hu2, hw2⟩
        · cases u with
          | inl i =>
            -- a left `3` plus another nonzero left label
            obtain ⟨i', hi'⟩ := Fintype.exists_ne_of_one_lt_card (by rw [Fintype.card_fin]; omega) i
            have := pairL i' i hi'
            have := Nat.one_le_iff_ne_zero.mpr (hA0 i')
            omega
          | inr j' => simp at hadj
        · cases u with
          | inr j' => simp at hu
          | inl i₁ =>
            cases w with
            | inr j' => simp at hw'
            | inl i₂ =>
              have := pairL i₁ i₂ (fun h => huw (by rw [h]))
              omega
      · push Not at hB0
        have hB : n ≤ ∑ j, f (Sum.inr j) := by
          calc n = ∑ _j : Fin n, 1 := by simp
            _ ≤ ∑ j, f (Sum.inr j) := Finset.sum_le_sum fun j _ => Nat.one_le_iff_ne_zero.mpr (hB0 j)
        omega
  have six_le : ∀ f : Fin m ⊕ Fin n → ℕ, 3 ≤ m → 3 ≤ n → IsDRDF (K m n) f → 6 ≤ weight f := by
    intro f hm hn hf
    -- left labels summing to `≤ 1` force every right label `≥ 2`
    have h3 : ∑ i, f (Sum.inl i) ≤ 1 → 6 ≤ weight f := by
      intro ha
      -- every left label is at most `1`
      have hle : ∀ i, f (Sum.inl i) ≤ 1 := fun i =>
        (Finset.single_le_sum (f := fun i => f (Sum.inl i)) (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ i)).trans ha
      -- so no right vertex can be labelled `0` or `1`: its neighbours are all on the left
      have hright : ∀ j, 2 ≤ f (Sum.inr j) := by
        intro j
        by_contra hlt
        push Not at hlt
        rcases Nat.lt_succ_iff.mp hlt |>.lt_or_eq with h0 | h1
        · have h0' : f (Sum.inr j) = 0 := by omega
          rcases hf.2.1 (Sum.inr j) h0' with ⟨u, hadj, hu⟩ | ⟨u, w, -, hu, -, hu2, -⟩
          · cases u with
            | inl i => have := hle i; omega
            | inr j' => simp at hadj
          · cases u with
            | inl i => have := hle i; omega
            | inr j' => simp at hu
        · obtain ⟨u, hadj, hu⟩ := hf.2.2 (Sum.inr j) h1
          cases u with
          | inl i => have := hle i; omega
          | inr j' => simp at hadj
      have hB : 2 * n ≤ ∑ j, f (Sum.inr j) := by
        calc 2 * n = ∑ _j : Fin n, 2 := by simp [mul_comm]
          _ ≤ ∑ j, f (Sum.inr j) := Finset.sum_le_sum fun j _ => hright j
      have hw : weight f = ∑ i, f (Sum.inl i) + ∑ j, f (Sum.inr j) := Fintype.sum_sum_type f
      omega
    -- right labels summing to `≤ 1` force every left label `≥ 2`
    have h4 : ∑ j, f (Sum.inr j) ≤ 1 → 6 ≤ weight f := by
      intro hb
      -- every right label is at most `1`
      have hle : ∀ j, f (Sum.inr j) ≤ 1 := fun j =>
        (Finset.single_le_sum (f := fun j => f (Sum.inr j)) (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ j)).trans hb
      -- so no left vertex can be labelled `0` or `1`: its neighbours are all on the right
      have hleft : ∀ i, 2 ≤ f (Sum.inl i) := by
        intro i
        by_contra hlt
        push Not at hlt
        rcases Nat.lt_succ_iff.mp hlt |>.lt_or_eq with h0 | h1
        · have h0' : f (Sum.inl i) = 0 := by omega
          rcases hf.2.1 (Sum.inl i) h0' with ⟨u, hadj, hu⟩ | ⟨u, w, -, hu, -, hu2, -⟩
          · cases u with
            | inl i' => simp at hadj
            | inr j => have := hle j; omega
          · cases u with
            | inl i' => simp at hu
            | inr j => have := hle j; omega
        · obtain ⟨u, hadj, hu⟩ := hf.2.2 (Sum.inl i) h1
          cases u with
          | inl i' => simp at hadj
          | inr j => have := hle j; omega
      have hA : 2 * m ≤ ∑ i, f (Sum.inl i) := by
        calc 2 * m = ∑ _i : Fin m, 2 := by simp [mul_comm]
          _ ≤ ∑ i, f (Sum.inl i) := Finset.sum_le_sum fun i _ => hleft i
      have hw : weight f = ∑ i, f (Sum.inl i) + ∑ j, f (Sum.inr j) := Fintype.sum_sum_type f
      omega
    -- a left `0` with left sum `≥ 2`
    have h6 : 2 ≤ ∑ i, f (Sum.inl i) → (∃ i, f (Sum.inl i) = 0) → 6 ≤ weight f := by
      intro ha h0
      have hw : weight f = ∑ i, f (Sum.inl i) + ∑ j, f (Sum.inr j) := Fintype.sum_sum_type f
      have singleL : ∀ i, f (Sum.inl i) ≤ ∑ i, f (Sum.inl i) := fun i =>
        Finset.single_le_sum (f := fun i => f (Sum.inl i)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      have pairL : ∀ a b : Fin m, a ≠ b → f (Sum.inl a) + f (Sum.inl b) ≤ ∑ i, f (Sum.inl i) := by
        intro a b hab
        rw [← Finset.sum_pair (f := fun i => f (Sum.inl i)) hab]
        exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
      have pairR : ∀ a b : Fin n, a ≠ b → f (Sum.inr a) + f (Sum.inr b) ≤ ∑ j, f (Sum.inr j) := by
        intro a b hab
        rw [← Finset.sum_pair (f := fun j => f (Sum.inr j)) hab]
        exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
      obtain ⟨i, hi⟩ := h0
      rcases hf.2.1 (Sum.inl i) hi with ⟨u, hadj, hu⟩ | ⟨u, w, huw, hu, hw', hu2, hw2⟩
      · cases u with
        | inl i' => simp at hadj
        | inr j =>
          -- a right `3`; if the left labels sum to exactly `2`, a second right label is nonzero
          by_cases hA3 : 3 ≤ ∑ i, f (Sum.inl i)
          · have : f (Sum.inr j) ≤ ∑ j, f (Sum.inr j) :=
              Finset.single_le_sum (f := fun j => f (Sum.inr j)) (fun _ _ => Nat.zero_le _)
                (Finset.mem_univ j)
            omega
          · obtain ⟨r, hr⟩ := Fintype.exists_ne_of_one_lt_card (by rw [Fintype.card_fin]; omega) j
            have hr0 : f (Sum.inr r) ≠ 0 := by
              intro hr0
              rcases hf.2.1 (Sum.inr r) hr0 with ⟨u, hadj, hu⟩ | ⟨u, w, huw, hu, hw', hu2, hw2⟩
              · cases u with
                | inl i' => have := singleL i'; omega
                | inr j' => simp at hadj
              · cases u with
                | inr j' => simp at hu
                | inl i₁ =>
                  cases w with
                  | inr j' => simp at hw'
                  | inl i₂ =>
                    have := pairL i₁ i₂ (fun h => huw (by rw [h]))
                    omega
            have := pairR r j hr
            omega
      · cases u with
        | inl i' => simp at hu
        | inr j₁ =>
          cases w with
          | inl i' => simp at hw'
          | inr j₂ =>
            have := pairR j₁ j₂ (fun h => huw (by rw [h]))
            omega
    -- no left `0` with right sum `≥ 2`
    have h7 : 2 ≤ ∑ j, f (Sum.inr j) → (∀ i, f (Sum.inl i) ≠ 0) → 6 ≤ weight f := by
      intro hb h0
      have hw : weight f = ∑ i, f (Sum.inl i) + ∑ j, f (Sum.inr j) := Fintype.sum_sum_type f
      by_cases hA4 : 4 ≤ ∑ i, f (Sum.inl i)
      · omega
      · -- left sum `≤ 3` with `m ≥ 3` nonzero labels: every left label is `1`
        have hle : ∀ i, f (Sum.inl i) ≤ 1 := by
          intro i
          have hsplit := Finset.add_sum_erase Finset.univ (fun i => f (Sum.inl i)) (Finset.mem_univ i)
          have hrest : m - 1 ≤ ∑ i' ∈ Finset.univ.erase i, f (Sum.inl i') := by
            calc m - 1 = ∑ _i' ∈ Finset.univ.erase i, 1 := by
                  rw [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_erase_of_mem (Finset.mem_univ i),
                    Finset.card_univ, Fintype.card_fin]
              _ ≤ ∑ i' ∈ Finset.univ.erase i, f (Sum.inl i') :=
                  Finset.sum_le_sum fun i' _ => Nat.one_le_iff_ne_zero.mpr (h0 i')
          simp only at hsplit
          omega
        -- hence every right label is at least `2`
        have hright : ∀ j, 2 ≤ f (Sum.inr j) := by
          intro j
          by_contra hlt
          push Not at hlt
          rcases Nat.lt_succ_iff.mp hlt |>.lt_or_eq with h0' | h1
          · have h0'' : f (Sum.inr j) = 0 := by omega
            rcases hf.2.1 (Sum.inr j) h0'' with ⟨u, hadj, hu⟩ | ⟨u, w, -, hu, -, hu2, -⟩
            · cases u with
              | inl i => have := hle i; omega
              | inr j' => simp at hadj
            · cases u with
              | inl i => have := hle i; omega
              | inr j' => simp at hu
          · obtain ⟨u, hadj, hu⟩ := hf.2.2 (Sum.inr j) h1
            cases u with
            | inl i => have := hle i; omega
            | inr j' => simp at hadj
        have hB : 2 * n ≤ ∑ j, f (Sum.inr j) := by
          calc 2 * n = ∑ _j : Fin n, 2 := by simp [mul_comm]
            _ ≤ ∑ j, f (Sum.inr j) := Finset.sum_le_sum fun j _ => hright j
        omega
    by_cases hA : ∑ i, f (Sum.inl i) ≤ 1
    · exact h3 hA
    by_cases hB : ∑ j, f (Sum.inr j) ≤ 1
    · exact h4 hB
    by_cases hz : ∃ i, f (Sum.inl i) = 0
    · exact h6 (by omega) hz
    · push Not at hz
      exact h7 (by omega) hz
  split_ifs with h1 h2
  · -- `min m n = 1`: a `3` on the singleton side
    refine key 3 ?_ three_le
    rcases (show m = 1 ∨ n = 1 by omega) with rfl | rfl
    · refine ⟨Sum.elim (fun _ => 3) (fun _ => 0), ⟨?_, ?_, ?_⟩, ?_⟩
      · intro v; cases v <;> simp
      · intro v hv
        cases v with
        | inl i => simp at hv
        | inr j => exact Or.inl ⟨Sum.inl 0, by simp, rfl⟩
      · intro v hv; cases v <;> simp at hv
      · simp [weight, Fintype.sum_sum_type]
    · refine ⟨Sum.elim (fun _ => 0) (fun _ => 3), ⟨?_, ?_, ?_⟩, ?_⟩
      · intro v; cases v <;> simp
      · intro v hv
        cases v with
        | inl i => exact Or.inl ⟨Sum.inr 0, by simp, rfl⟩
        | inr j => simp at hv
      · intro v hv; cases v <;> simp at hv
      · simp [weight, Fintype.sum_sum_type]
  · -- `min m n = 2`: `2` on both vertices of a side of size two
    refine key 4 ?_ (fun f hf => four_le f (by omega) (by omega) hf)
    rcases (show m = 2 ∨ n = 2 by omega) with rfl | rfl
    · refine ⟨Sum.elim (fun _ => 2) (fun _ => 0), ⟨?_, ?_, ?_⟩, ?_⟩
      · intro v; cases v <;> simp
      · intro v hv
        cases v with
        | inl i => simp at hv
        | inr j =>
          refine Or.inr ⟨Sum.inl 0, Sum.inl 1, by simp, by simp, by simp, by simp, by simp⟩
      · intro v hv; cases v <;> simp at hv
      · simp [weight, Fintype.sum_sum_type]
    · refine ⟨Sum.elim (fun _ => 0) (fun _ => 2), ⟨?_, ?_, ?_⟩, ?_⟩
      · intro v; cases v <;> simp
      · intro v hv
        cases v with
        | inl i =>
          refine Or.inr ⟨Sum.inr 0, Sum.inr 1, by simp, by simp, by simp, by simp, by simp⟩
        | inr j => simp at hv
      · intro v hv; cases v <;> simp at hv
      · simp [weight, Fintype.sum_sum_type]
  · -- `m, n ≥ 3`: a `3` on one vertex of each side
    refine key 6 ?_ (fun f hf => six_le f (by omega) (by omega) hf)
    have hm0 : 0 < m := by omega
    have hn0 : 0 < n := by omega
    refine ⟨Sum.elim (fun i => if i = ⟨0, hm0⟩ then 3 else 0)
      (fun j => if j = ⟨0, hn0⟩ then 3 else 0), ⟨?_, ?_, ?_⟩, ?_⟩
    · intro v
      cases v <;> simp only [Sum.elim_inl, Sum.elim_inr] <;> split_ifs <;> omega
    · intro v hv
      cases v with
      | inl i => exact Or.inl ⟨Sum.inr ⟨0, hn0⟩, by simp, by simp⟩
      | inr j => exact Or.inl ⟨Sum.inl ⟨0, hm0⟩, by simp, by simp⟩
    · intro v hv
      cases v <;> simp only [Sum.elim_inl, Sum.elim_inr] at hv <;> split_ifs at hv <;> omega
    · simp only [weight, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]
