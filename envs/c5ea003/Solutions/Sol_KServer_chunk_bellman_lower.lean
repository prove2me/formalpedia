-- Prove2me | solution 1 for KServer.chunk_bellman_lower
-- status  : ACCEPTED   (prove)
-- author  : @kwal0203
-- created : 2026-10-30T03:05:57.868122+00:00
-- url     : https://prove2.me/submissions/c25ea826-4550-4557-82c4-94e18ea99b14

import Definitions.Def_KServer_chunk_bellman

open KServer

private theorem cost_append_single {X : Type*} [MetricSpace X]
    (E : EvaderAlgorithm X) (h : List (Set X)) (S : Set X) :
    E.cost (h ++ [S]) = E.cost h + dist (E.pos h) (E.pos (h ++ [S])) := by
  have hpre : (∑ j ∈ Finset.range h.length,
      dist (E.pos ((h ++ [S]).take j)) (E.pos ((h ++ [S]).take (j + 1)))) = E.cost h := by
    unfold EvaderAlgorithm.cost
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' := Finset.mem_range.mp hj
    rw [List.take_append_of_le_length (by omega : j ≤ h.length),
      List.take_append_of_le_length (by omega : j + 1 ≤ h.length)]
  unfold EvaderAlgorithm.cost
  simp only [List.length_append, List.length_singleton]
  rw [Finset.sum_range_succ, hpre]
  have hfull : (h ++ [S]).take (h.length + 1) = h ++ [S] := by
    apply List.take_of_length_le
    simp
  change E.cost h + dist (E.pos ((h ++ [S]).take h.length))
    (E.pos ((h ++ [S]).take (h.length + 1))) = E.cost h + _
  rw [List.take_append_length, hfull]

private theorem costOn_cons {X : Type*} [MetricSpace X]
    (E : EvaderAlgorithm X) (h : List (Set X)) (S : Set X) (χ : List (Set X)) :
    E.costOn h (S :: χ) = dist (E.pos h) (E.pos (h ++ [S])) + E.costOn (h ++ [S]) χ := by
  have heq : h ++ S :: χ = (h ++ [S]) ++ χ := by simp
  unfold EvaderAlgorithm.costOn
  rw [heq, cost_append_single]
  ring

private theorem bailTime_cons {X : Type*} (b : List (Set X) → Bool)
    (h : List (Set X)) (S : Set X) (χ : List (Set X)) :
    bailTime b h (S :: χ) =
      if b h then some 0 else (bailTime b (h ++ [S]) χ).map Nat.succ := by
  unfold bailTime
  simp only [List.length_cons, List.range_succ_eq_map, List.find?_cons,
    List.take_zero, List.append_nil, List.find?_map]
  cases hb : b h with
  | true => simp [hb]
  | false =>
    simp only [hb, Bool.false_eq_true, if_false]
    congr 2
    funext q
    simp [Function.comp_def, List.take_succ_cons, List.append_assoc]

private theorem bailCost_nil {X : Type*} [MetricSpace X]
    (E : EvaderAlgorithm X) (b : List (Set X) → Bool) (h : List (Set X)) (p : ℝ) :
    E.bailCost b h [] p = 0 := by
  simp [EvaderAlgorithm.bailCost, bailTime, EvaderAlgorithm.costOn]

private theorem bailCost_cons {X : Type*} [MetricSpace X]
    (E : EvaderAlgorithm X) (b : List (Set X) → Bool)
    (h : List (Set X)) (S : Set X) (χ : List (Set X)) (p : ℝ) :
    E.bailCost b h (S :: χ) p = if b h then p else
      dist (E.pos h) (E.pos (h ++ [S])) + E.bailCost b (h ++ [S]) χ p := by
  unfold EvaderAlgorithm.bailCost
  rw [bailTime_cons]
  cases hb : b h with
  | true => simp [EvaderAlgorithm.costOn]
  | false =>
    simp only [Bool.false_eq_true, if_false]
    cases ht : bailTime b (h ++ [S]) χ with
    | none => simpa only [Option.map_none] using costOn_cons E h S χ
    | some q =>
      simp only [Option.map_some, List.take_succ_cons]
      rw [costOn_cons]
      ring

theorem solution {X : Type*} [MetricSpace X] [Fintype X]
    {Ω : Type*} [Fintype Ω] (p : ℝ) (n : ℕ) (P : Ω → ℝ)
    (σ : Ω → List (Set X)) (hP : ∀ ω, 0 ≤ P ω)
    (hlen : ∀ ω, (σ ω).length ≤ n)
    (hne : ∀ ω, ∀ S ∈ σ ω, S.Nonempty)
    (E : EvaderAlgorithm X) (b : List (Set X) → Bool) (h : List (Set X)) :
    chunkBellman p n P σ (E.pos h) ≤ ∑ ω, P ω * E.bailCost b h (σ ω) p := by
  classical
  induction n generalizing P σ h with
  | zero =>
    have hs : ∀ ω, σ ω = [] := by
      intro ω
      have := hlen ω
      cases heq : σ ω <;> simp_all
    simp [chunkBellman, hs, bailCost_nil]
  | succ n ih =>
    have htail : ∀ ω, ((σ ω).tail).length ≤ n := by
      intro ω
      have := hlen ω
      cases hs : σ ω <;> simp [hs] at this ⊢ <;> omega
    have htailne : ∀ ω, ∀ S ∈ (σ ω).tail, S.Nonempty :=
      fun ω S hS => hne ω S (List.mem_of_mem_tail hS)
    by_cases hb : b h = true
    · refine le_trans (min_le_left _ _) ?_
      change p * (∑ ω, if σ ω = [] then 0 else P ω) ≤ _
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro ω _
      cases hs : σ ω with
      | nil => simp [bailCost_nil]
      | cons S χ => simp [bailCost_cons, hb, mul_comm]
    · have hb' : b h = false := Bool.eq_false_iff.mpr hb
      refine le_trans (min_le_right _ _) ?_
      change (∑ S : Set X, if hS : S.Nonempty then
        (Finset.univ.filter (fun y : X => y ∈ S)).inf' _ (fun y =>
          (∑ ω, if (σ ω).head? = some S then P ω else 0) * dist (E.pos h) y +
            chunkBellman p n (fun ω => if (σ ω).head? = some S then P ω else 0)
              (fun ω => (σ ω).tail) y) else 0) ≤ _
      calc
        _ ≤ ∑ S : Set X, ∑ ω,
            if (σ ω).head? = some S then P ω *
              (dist (E.pos h) (E.pos (h ++ [S])) + E.bailCost b (h ++ [S]) ((σ ω).tail) p)
            else 0 := by
          apply Finset.sum_le_sum
          intro S _
          by_cases hS : S.Nonempty
          · rw [dif_pos hS]
            have hmem : E.pos (h ++ [S]) ∈ Finset.univ.filter (fun y : X => y ∈ S) := by
              simp only [Finset.mem_filter, Finset.mem_univ, true_and]
              exact E.serves h S hS
            refine (Finset.inf'_le _ hmem).trans ?_
            have hind := ih (fun ω => if (σ ω).head? = some S then P ω else 0)
              (fun ω => (σ ω).tail)
              (by intro ω; dsimp; split <;> simp_all) htail htailne (h ++ [S])
            have heq : (∑ ω, if (σ ω).head? = some S then P ω else 0) *
                dist (E.pos h) (E.pos (h ++ [S])) +
                (∑ ω, (if (σ ω).head? = some S then P ω else 0) *
                  E.bailCost b (h ++ [S]) ((σ ω).tail) p)
                = ∑ ω, if (σ ω).head? = some S then P ω *
                  (dist (E.pos h) (E.pos (h ++ [S])) + E.bailCost b (h ++ [S]) ((σ ω).tail) p)
                  else 0 := by
              rw [Finset.sum_mul, ← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl
              intro ω _
              split <;> simp_all <;> ring
            rw [← heq]
            linarith
          · rw [dif_neg hS]
            have hn : ∀ ω, (σ ω).head? ≠ some S := by
              intro ω heq
              have hm : S ∈ σ ω := List.mem_of_head? heq
              exact hS (hne ω S hm)
            simp [hn]
        _ = ∑ ω, P ω * E.bailCost b h (σ ω) p := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro ω _
          cases hs : σ ω with
          | nil => simp [bailCost_nil]
          | cons S χ => simp [bailCost_cons, hb', eq_comm]
