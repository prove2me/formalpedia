-- Prove2me | solution 2 for KitchenQuery.tasteCost_le_card_ingredients
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T06:34:19.093361+00:00
-- url     : https://prove2.me/submissions/295e3998-1229-4080-b7f0-c9bdec6044cf

import Definitions.Def_Novelty_KitchenQueryComplexity

open KitchenQuery Finset

open KitchenQuery Finset in
/-- **Tasting is never slower than cooking.** -/
theorem solution {n : ℕ} (f : Dish n) : tasteCost f ≤ cookCost f := by
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
  exact cost_le f
