-- Prove2me | solution 1 for KServer.exists_lazy_algorithm
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-31T01:21:05.730356+00:00
-- url     : https://prove2.me/submissions/8eef28a0-5266-4db7-886c-ab1fdc1f5d07

import Mathlib
import Definitions.Def_KServer_model

open KServer

/-- Splitting the cost of an online algorithm at the last request. -/
private theorem cost_concat {k : ℕ} {M : Type} [MetricSpace M]
    (X : OnlineAlgorithm k M) (l : List M) (r : M) :
    X.cost (l ++ [r]) = X.cost l + moveCost (X.conf l) (X.conf (l ++ [r])) := by
  unfold OnlineAlgorithm.cost
  have hlen : (l ++ [r]).length = l.length + 1 := by simp
  rw [hlen, Finset.sum_range_succ]
  congr 1
  · refine Finset.sum_congr rfl ?_
    intro j hj
    simp only [Finset.mem_range] at hj
    rw [List.take_append_of_le_length (by omega), List.take_append_of_le_length (by omega)]
  · rw [List.take_append_of_le_length (le_refl _), List.take_length,
      List.take_of_length_le (by simp)]

theorem solution (k : ℕ) (M : Type) [MetricSpace M]
    (A : OnlineAlgorithm k M) :
    ∃ B : OnlineAlgorithm k M,
      B.conf [] = A.conf [] ∧
      (∀ σ : List M, B.cost σ ≤ A.cost σ) ∧
      (∀ (l : List M) (r : M), ∃ i : Fin k,
        B.conf (l ++ [r]) = Function.update (B.conf l) i r) := by
  classical
  -- `idx l r` is a server that `A` places on the request `r` after the list `l`.
  set idx : List M → M → Fin k := fun l r => (A.serves l r).choose with hidxdef
  have hidx : ∀ (l : List M) (r : M), A.conf (l ++ [r]) (idx l r) = r :=
    fun l r => (A.serves l r).choose_spec
  -- the lazy simulator: it moves the server with the *same index* onto the request
  set bconf : List M → Config k M := fun l =>
    List.reverseRecOn l (A.conf []) (fun l r prev => Function.update prev (idx l r) r)
    with hbdef
  have hb_nil : bconf [] = A.conf [] := by simp [hbdef]
  have hb_concat : ∀ (l : List M) (r : M),
      bconf (l ++ [r]) = Function.update (bconf l) (idx l r) r := by
    intro l r; simp [hbdef]
  -- `B` is a genuine online algorithm: after `l ++ [r]` the server `idx l r` sits on `r`.
  refine ⟨⟨bconf, ?_⟩, hb_nil, ?_, ?_⟩
  · intro l r
    exact ⟨idx l r, by rw [hb_concat l r]; simp⟩
  · -- the potential argument
    have main : ∀ l : List M,
        (∑ j ∈ Finset.range l.length,
            moveCost (bconf (l.take j)) (bconf (l.take (j + 1))))
          + moveCost (bconf l) (A.conf l) ≤ A.cost l := by
      intro l
      induction l using List.reverseRecOn with
      | nil => simp [OnlineAlgorithm.cost, moveCost, hb_nil]
      | append_singleton l r ih =>
        -- notation: `a`/`a'` are A's configurations before/after, `b` is B's, `j` the moved server
        set j : Fin k := idx l r with hjdef
        set a : Config k M := A.conf l with hadef
        set a' : Config k M := A.conf (l ++ [r]) with ha'def
        set b : Config k M := bconf l with hbdefl
        have ha'j : a' j = r := hidx l r
        -- B's cost splits off the last step, exactly as A's does
        have hsplit : (∑ i ∈ Finset.range (l ++ [r]).length,
              moveCost (bconf ((l ++ [r]).take i)) (bconf ((l ++ [r]).take (i + 1))))
            = (∑ i ∈ Finset.range l.length,
              moveCost (bconf (l.take i)) (bconf (l.take (i + 1))))
              + moveCost b (bconf (l ++ [r])) := by
          have hlen : (l ++ [r]).length = l.length + 1 := by simp
          rw [hlen, Finset.sum_range_succ]
          congr 1
          · refine Finset.sum_congr rfl ?_
            intro i hi
            simp only [Finset.mem_range] at hi
            rw [List.take_append_of_le_length (by omega),
              List.take_append_of_le_length (by omega)]
          · rw [List.take_append_of_le_length (le_refl _), List.take_length,
              List.take_of_length_le (by simp)]
        -- the single move of B costs `dist (b j) r`
        have hΔB : moveCost b (bconf (l ++ [r])) = dist (b j) r := by
          rw [hb_concat l r, ← hbdefl, ← hjdef]
          unfold moveCost
          rw [Finset.sum_eq_single j (fun i _ hij => by simp [Function.update_of_ne hij])
            (by simp)]
          simp
        -- the new potential only runs over the servers other than `j`
        have hΦ' : moveCost (bconf (l ++ [r])) a'
            = ∑ i ∈ Finset.univ.erase j, dist (b i) (a' i) := by
          rw [hb_concat l r, ← hbdefl, ← hjdef]
          unfold moveCost
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
          rw [Function.update_self, ha'j, dist_self, zero_add]
          exact Finset.sum_congr rfl fun i hi => by
            rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
        -- split A's step cost and the old potential at the index `j`
        have hΔA : moveCost a a' = dist (a j) (a' j)
            + ∑ i ∈ Finset.univ.erase j, dist (a i) (a' i) :=
          (Finset.add_sum_erase _ _ (Finset.mem_univ j)).symm
        have hΦ : moveCost b a = dist (b j) (a j)
            + ∑ i ∈ Finset.univ.erase j, dist (b i) (a i) :=
          (Finset.add_sum_erase _ _ (Finset.mem_univ j)).symm
        -- triangle inequality, server by server
        have htri_j : dist (b j) r ≤ dist (b j) (a j) + dist (a j) (a' j) := by
          rw [← ha'j]; exact dist_triangle _ _ _
        have htri_rest : (∑ i ∈ Finset.univ.erase j, dist (b i) (a' i))
            ≤ (∑ i ∈ Finset.univ.erase j, dist (b i) (a i))
              + ∑ i ∈ Finset.univ.erase j, dist (a i) (a' i) := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_le_sum fun i _ => dist_triangle _ _ _
        rw [hsplit, hΔB, hΦ', cost_concat A l r, ← hadef, ← ha'def]
        rw [hΔA] at *
        rw [hΦ] at ih
        linarith
    intro σ
    have h := main σ
    have hΦ : 0 ≤ moveCost (bconf σ) (A.conf σ) :=
      Finset.sum_nonneg fun i _ => dist_nonneg
    have : (⟨bconf, by intro l r; exact ⟨idx l r, by rw [hb_concat l r]; simp⟩⟩ :
        OnlineAlgorithm k M).cost σ
        = ∑ j ∈ Finset.range σ.length,
            moveCost (bconf (σ.take j)) (bconf (σ.take (j + 1))) := rfl
    linarith
  · intro l r
    exact ⟨idx l r, hb_concat l r⟩
