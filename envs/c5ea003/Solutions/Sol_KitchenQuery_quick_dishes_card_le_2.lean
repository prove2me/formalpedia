-- Prove2me | solution 2 for KitchenQuery.quick_dishes_card_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T06:52:09.515025+00:00
-- url     : https://prove2.me/submissions/a96e2533-e012-4e56-acce-d366c50d8cde

import Definitions.Def_Novelty_KitchenQueryComplexity

open KitchenQuery Finset

open KitchenQuery Finset in
/-- **At most `2n + 2` dishes can be judged with a single probe.** -/
theorem solution {n : ℕ} :
    (Finset.univ.filter (fun f : Dish n => tasteCost f ≤ 1)).card ≤ 2 * n + 2 := by
  classical
  -- (A) correctness of the brute-force taster
  have brute_eval : ∀ (f : Dish n) (k : ℕ) (a x : Pantry n),
      (brute f k a).eval x = f (fun i => if (i : ℕ) < k then x i else a i) := by
    intro f k
    induction k with
    | zero =>
        intro a x
        simp [brute, Taste.eval]
    | succ k ih =>
        intro a x
        by_cases hk : k < n
        · rw [brute, dif_pos hk]
          simp only [Taste.eval]
          cases hxk : x ⟨k, hk⟩
          · rw [if_neg (by simp), ih]
            congr 1
            funext i
            by_cases h1 : (i : ℕ) < k
            · simp [h1, Nat.lt_succ_of_lt h1]
            · by_cases h2 : (i : ℕ) = k
              · have hi : i = ⟨k, hk⟩ := Fin.ext h2
                subst hi
                simp [hxk]
              · have h3 : ¬ (i : ℕ) < k + 1 := by omega
                have hne : i ≠ ⟨k, hk⟩ := fun e => h2 (congrArg Fin.val e)
                simp [h1, h3, Function.update_of_ne hne]
          · rw [if_pos rfl, ih]
            congr 1
            funext i
            by_cases h1 : (i : ℕ) < k
            · simp [h1, Nat.lt_succ_of_lt h1]
            · by_cases h2 : (i : ℕ) = k
              · have hi : i = ⟨k, hk⟩ := Fin.ext h2
                subst hi
                simp [hxk]
              · have h3 : ¬ (i : ℕ) < k + 1 := by omega
                have hne : i ≠ ⟨k, hk⟩ := fun e => h2 (congrArg Fin.val e)
                simp [h1, h3, Function.update_of_ne hne]
        · rw [brute, dif_neg hk, ih]
          congr 1
          funext i
          have h1 : (i : ℕ) < k := by omega
          have h2 : (i : ℕ) < k + 1 := by omega
          simp [h1, h2]
  -- (B) depth of the brute-force taster
  have brute_depth : ∀ (f : Dish n) (k : ℕ) (a : Pantry n), (brute f k a).depth ≤ k := by
    intro f k
    induction k with
    | zero => intro a; simp [brute, Taste.depth]
    | succ k ih =>
        intro a
        by_cases hk : k < n
        · rw [brute, dif_pos hk]
          simp only [Taste.depth]
          have := ih (Function.update a ⟨k, hk⟩ false)
          have := ih (Function.update a ⟨k, hk⟩ true)
          omega
        · rw [brute, dif_neg hk]
          have := ih a
          omega
  -- (C) tasting is never slower than cooking
  have mem_depths : ∀ f : Dish n, n ∈ tasteDepths f := by
    intro f
    refine ⟨brute f n (fun _ => false), ?_, brute_depth f n _⟩
    intro x
    rw [brute_eval]
    congr 1
    funext i
    simp [i.2]
  have cost_le : ∀ f : Dish n, tasteCost f ≤ n := fun f => Nat.sInf_le (mem_depths f)
  have classify : ∀ f : Dish n, tasteCost f ≤ 1 →
      (∃ b, ∀ x, f x = b) ∨ ∃ i : Fin n, (∀ x, f x = x i) ∨ (∀ x, f x = !x i) := by
    intro f hf
    obtain ⟨t, ht, hd⟩ := Nat.sInf_mem ⟨n, mem_depths f⟩
    have hd' : t.depth ≤ 1 := le_trans hd hf
    cases t with
    | serve b => exact Or.inl ⟨b, fun x => (ht x).symm⟩
    | probe i l r =>
        cases l with
        | probe _ _ _ => simp only [Taste.depth] at hd'; omega
        | serve b1 =>
          cases r with
          | probe _ _ _ => simp only [Taste.depth] at hd'; omega
          | serve b2 =>
            have hf' : ∀ x, f x = if x i then b2 else b1 := fun x => by rw [← ht x]; rfl
            cases b1 <;> cases b2
            · exact Or.inl ⟨false, fun x => by rw [hf']; split_ifs <;> rfl⟩
            · exact Or.inr ⟨i, Or.inl (fun x => by rw [hf']; cases x i <;> rfl)⟩
            · exact Or.inr ⟨i, Or.inr (fun x => by rw [hf']; cases x i <;> rfl)⟩
            · exact Or.inl ⟨true, fun x => by rw [hf']; split_ifs <;> rfl⟩
  let g : Bool ⊕ (Fin n × Bool) → Dish n := fun s => match s with
    | Sum.inl b => fun _ => b
    | Sum.inr (i, true) => fun x => x i
    | Sum.inr (i, false) => fun x => !x i
  have hsub : Finset.univ.filter (fun f : Dish n => tasteCost f ≤ 1) ⊆ Finset.univ.image g := by
    intro f hf
    rw [Finset.mem_filter] at hf
    rw [Finset.mem_image]
    rcases classify f hf.2 with ⟨b, hb⟩ | ⟨i, hi | hi⟩
    · exact ⟨Sum.inl b, Finset.mem_univ _, funext fun x => (hb x).symm⟩
    · exact ⟨Sum.inr (i, true), Finset.mem_univ _, funext fun x => (hi x).symm⟩
    · exact ⟨Sum.inr (i, false), Finset.mem_univ _, funext fun x => (hi x).symm⟩
  calc (Finset.univ.filter (fun f : Dish n => tasteCost f ≤ 1)).card
      ≤ (Finset.univ.image g).card := Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (Bool ⊕ (Fin n × Bool))).card := Finset.card_image_le
    _ = 2 * n + 2 := by
      rw [Finset.card_univ, Fintype.card_sum, Fintype.card_prod, Fintype.card_bool, Fintype.card_fin]
      ring
