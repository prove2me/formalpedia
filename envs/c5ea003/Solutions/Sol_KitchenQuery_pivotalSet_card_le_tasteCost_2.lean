-- Prove2me | solution 2 for KitchenQuery.pivotalSet_card_le_tasteCost
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T06:30:33.576536+00:00
-- url     : https://prove2.me/submissions/54bdf6ab-bb88-4d9b-861d-0e501f5f3570

import Definitions.Def_Novelty_KitchenQueryComplexity

open KitchenQuery Finset

open KitchenQuery Finset in
/-- **Sensitivity is a lower bound on tasting time.** -/
theorem solution {n : ℕ} (f : Dish n) (x : Pantry n) :
    (pivotalSet f x).card ≤ tasteCost f := by
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
  -- (D) path lemmas
  have eval_agree : ∀ (t : Taste n) (x y : Pantry n), (∀ i ∈ t.path x, y i = x i) →
      t.eval y = t.eval x := by
    intro t
    induction t with
    | serve b => intro x y _; rfl
    | probe j l r ihl ihr =>
        intro x y hxy
        have hj : y j = x j := hxy j (by simp [Taste.path])
        simp only [Taste.eval, hj]
        split_ifs with hx
        · exact ihr x y (fun i hi => hxy i (by simp [Taste.path, hx, hi]))
        · exact ihl x y (fun i hi => hxy i (by simp [Taste.path, hx, hi]))
  have card_path : ∀ (t : Taste n) (x : Pantry n), (t.path x).card ≤ t.depth := by
    intro t
    induction t with
    | serve b => intro x; simp [Taste.path]
    | probe j l r ihl ihr =>
        intro x
        simp only [Taste.path, Taste.depth]
        refine (Finset.card_insert_le _ _).trans ?_
        split_ifs
        · have := ihr x; omega
        · have := ihl x; omega
  -- (E) sensitivity lower bound
  have sens : ∀ (f : Dish n) (x : Pantry n), (pivotalSet f x).card ≤ tasteCost f := by
    intro f x
    obtain ⟨t, ht, hd⟩ := Nat.sInf_mem ⟨n, mem_depths f⟩
    have hsub : pivotalSet f x ⊆ t.path x := by
      intro i hi
      by_contra hni
      simp only [pivotalSet, Finset.mem_filter, Finset.mem_univ, true_and, Pivotal] at hi
      apply hi
      rw [← ht, ← ht]
      apply eval_agree
      intro j hj
      have hji : j ≠ i := fun e => hni (e ▸ hj)
      exact Function.update_of_ne hji _ _
    exact (Finset.card_le_card hsub).trans ((card_path t x).trans hd)
  exact sens f x
