-- Prove2me | solution 1 for KServer.ckPotAtK_snoc_of_anchor_last
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-09T16:10:41.20586+00:00
-- url     : https://prove2.me/submissions/7e8c5248-6779-4d76-9ea0-e3c0aec5f214

import Mathlib
import Definitions.Def_KServer_ck_potential_k

/-!
# The anchored Coester–Koutsoupias potential shifts by the antipodal growth

If the last anchor of a tuple `x` is the request `r`, then all but one of the `k+1`
configurations occurring in `ckPotAtK` contain the request `Sum.inl r`, so their work
function values are unchanged by the request; the remaining one is the coalesced
antipode `r̄ ^ k`.  Hence the whole anchored potential grows by exactly the growth of
the work function at `r̄ ^ k`.
-/

namespace CKB

open KServer

section General

variable {k : ℕ} {N : Type} [MetricSpace N]

/-- The set of costs whose infimum defines `workFn`. -/
private def costSet (C₀ : Config k N) (σ : List N) (X : Config k N) : Set ℝ :=
  {c : ℝ | ∃ S : ℕ → Config k N, ServesFrom C₀ σ S ∧
    c = (∑ j ∈ Finset.range σ.length, moveCost (S j) (S (j + 1)))
        + moveCost (S σ.length) X}

private theorem workFn_eq_sInf (C₀ : Config k N) (σ : List N) (X : Config k N) :
    workFn C₀ σ X = sInf (costSet C₀ σ X) := rfl

private theorem moveCost_nonneg (C C' : Config k N) : 0 ≤ moveCost C C' :=
  Finset.sum_nonneg fun _ _ => dist_nonneg

private theorem moveCost_self (C : Config k N) : moveCost C C = 0 := by
  simp [moveCost]

private theorem moveCost_tri (A B C : Config k N) :
    moveCost A C ≤ moveCost A B + moveCost B C := by
  simpa [moveCost, ← Finset.sum_add_distrib] using
    Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => dist_triangle (A i) (B i) (C i))

private theorem costSet_bddBelow (C₀ : Config k N) (σ : List N) (X : Config k N) :
    BddBelow (costSet C₀ σ X) := by
  refine ⟨0, ?_⟩
  rintro c ⟨S, -, rfl⟩
  have h1 : (0:ℝ) ≤ ∑ j ∈ Finset.range σ.length, moveCost (S j) (S (j + 1)) :=
    Finset.sum_nonneg fun _ _ => moveCost_nonneg _ _
  have h2 := moveCost_nonneg (S σ.length) X
  linarith

/-- A schedule serving any request sequence exists as soon as there is at least one server. -/
private theorem exists_serves (hk : 0 < k) (C₀ : Config k N) (σ : List N) :
    ∃ S : ℕ → Config k N, ServesFrom C₀ σ S := by
  classical
  refine ⟨fun j => if j = 0 then C₀ else
      Function.update C₀ ⟨0, hk⟩ (σ.getD (j - 1) (C₀ ⟨0, hk⟩)), by simp, ?_⟩
  intro j
  refine ⟨⟨0, hk⟩, ?_⟩
  have h1 : ((j : ℕ) + 1) ≠ 0 := by omega
  simp only [h1, if_false, Nat.add_sub_cancel, Function.update_self]
  rw [List.getD_eq_getElem _ _ j.isLt]
  simp

private theorem costSet_nonempty (hk : 0 < k) (C₀ : Config k N) (σ : List N) (X : Config k N) :
    (costSet C₀ σ X).Nonempty := by
  obtain ⟨S, hS⟩ := exists_serves hk C₀ σ
  exact ⟨_, S, hS, rfl⟩

private theorem workFn_le_of_mem {C₀ : Config k N} {σ : List N} {X : Config k N} {c : ℝ}
    (hc : c ∈ costSet C₀ σ X) : workFn C₀ σ X ≤ c :=
  csInf_le (costSet_bddBelow _ _ _) hc

private theorem le_workFn (hk : 0 < k) {C₀ : Config k N} {σ : List N} {X : Config k N} {b : ℝ}
    (h : ∀ c ∈ costSet C₀ σ X, b ≤ c) : b ≤ workFn C₀ σ X :=
  le_csInf (costSet_nonempty hk C₀ σ X) h

/-- Serving one more request cannot decrease the work function. -/
private theorem workFn_le_snoc (hk : 0 < k) (C₀ : Config k N) (σ : List N) (q : N)
    (X : Config k N) : workFn C₀ σ X ≤ workFn C₀ (σ ++ [q]) X := by
  refine le_workFn hk ?_
  rintro c ⟨S, ⟨hS0, hS⟩, rfl⟩
  have hlen : (σ ++ [q]).length = σ.length + 1 := by simp
  -- the same schedule serves `σ`
  have hserv : ServesFrom C₀ σ S := by
    refine ⟨hS0, ?_⟩
    intro j
    obtain ⟨i, hi⟩ := hS ⟨(j : ℕ), by rw [hlen]; omega⟩
    exact ⟨i, by
      rw [hi]
      simp [List.get_eq_getElem, List.getElem_append, j.isLt]⟩
  have hmem : (∑ j ∈ Finset.range σ.length, moveCost (S j) (S (j + 1)))
      + moveCost (S σ.length) X ∈ costSet C₀ σ X := ⟨S, hserv, rfl⟩
  have h1 := workFn_le_of_mem hmem
  have h2 : moveCost (S σ.length) X
      ≤ moveCost (S σ.length) (S (σ.length + 1)) + moveCost (S (σ.length + 1)) X :=
    moveCost_tri _ _ _
  have h3 : (∑ j ∈ Finset.range (σ ++ [q]).length, moveCost (S j) (S (j + 1)))
      = (∑ j ∈ Finset.range σ.length, moveCost (S j) (S (j + 1)))
        + moveCost (S σ.length) (S (σ.length + 1)) := by
    rw [hlen, Finset.sum_range_succ]
  rw [h3, hlen]
  linarith

/-- Extending a schedule for `σ` by one final configuration `Y` containing `q`. -/
private theorem workFn_snoc_le (hk : 0 < k) (C₀ : Config k N) (σ : List N) (q : N)
    (X Y : Config k N) (hY : ∃ i, Y i = q) :
    workFn C₀ (σ ++ [q]) X ≤ workFn C₀ σ Y + moveCost Y X := by
  classical
  obtain ⟨i₀, hi₀⟩ := hY
  have key : ∀ c ∈ costSet C₀ σ Y, workFn C₀ (σ ++ [q]) X ≤ c + moveCost Y X := by
    rintro c ⟨S, ⟨hS0, hS⟩, rfl⟩
    set T : ℕ → Config k N := fun j => if j ≤ σ.length then S j else Y with hT
    have hTle : ∀ j, j ≤ σ.length → T j = S j := by
      intro j hj; simp only [hT]; rw [if_pos hj]
    have hTgt : ∀ j, ¬ j ≤ σ.length → T j = Y := by
      intro j hj; simp only [hT]; rw [if_neg hj]
    refine workFn_le_of_mem ⟨T, ⟨?_, ?_⟩, ?_⟩
    · rw [hTle 0 (Nat.zero_le _)]; exact hS0
    · intro j
      have hjlt : (j : ℕ) < σ.length + 1 := by have := j.isLt; simpa using this
      rcases Nat.lt_or_ge (j : ℕ) σ.length with hj | hj
      · obtain ⟨i, hi⟩ := hS ⟨(j : ℕ), hj⟩
        refine ⟨i, ?_⟩
        rw [hTle _ (by omega), hi]
        simp [List.get_eq_getElem, List.getElem_append, hj]
      · have hj' : (j : ℕ) = σ.length := by omega
        refine ⟨i₀, ?_⟩
        rw [hTgt _ (by omega), hi₀]
        simp [List.get_eq_getElem, List.getElem_append, hj']
    · have hlen : (σ ++ [q]).length = σ.length + 1 := by simp
      rw [hlen, Finset.sum_range_succ]
      have h1 : ∀ j ∈ Finset.range σ.length,
          moveCost (T j) (T (j+1)) = moveCost (S j) (S (j+1)) := by
        intro j hj
        simp only [Finset.mem_range] at hj
        rw [hTle _ (by omega), hTle _ (by omega)]
      rw [Finset.sum_congr rfl h1, hTle _ (le_refl _), hTgt _ (by omega)]
  have h2 : workFn C₀ (σ ++ [q]) X - moveCost Y X ≤ workFn C₀ σ Y :=
    le_csInf (costSet_nonempty hk C₀ σ Y) (fun c hc => by have := key c hc; linarith)
  linarith

/-- A configuration that already contains the new request has an unchanged work function. -/
private theorem workFn_snoc_of_mem (hk : 0 < k) (C₀ : Config k N) (σ : List N) (q : N)
    (X : Config k N) (hX : ∃ i, X i = q) :
    workFn C₀ (σ ++ [q]) X = workFn C₀ σ X := by
  refine le_antisymm ?_ (workFn_le_snoc hk C₀ σ q X)
  have := workFn_snoc_le hk C₀ σ q X X hX
  rwa [moveCost_self, add_zero] at this

/-- The unordered version: a configuration containing the new request is stationary. -/
theorem workFnU_snoc_of_mem (hk : 0 < k) (C₀ : Config k N) (σ : List N) (q : N)
    (X : Config k N) (hX : ∃ i, X i = q) :
    workFnU C₀ (σ ++ [q]) X = workFnU C₀ σ X := by
  unfold workFnU
  refine iInf_congr ?_
  intro π
  refine workFn_snoc_of_mem hk C₀ σ q _ ?_
  obtain ⟨i, hi⟩ := hX
  exact ⟨π.symm i, by simpa using hi⟩

end General

end CKB

open KServer

/-- Requesting `r` shifts the anchored potential of every anchor tuple whose last
coordinate is `r` by exactly the growth of the work function at the coalesced
antipode `r̄ ^ k`. -/
theorem solution (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M] (Δ : ℝ) (hΔ0 : 0 < Δ)
    (hΔ : ∀ x y : M, dist x y ≤ Δ) (C₀ : Config k M) (l : List M) (r : M)
    (x : Fin k → M) (hx : x ⟨k - 1, by omega⟩ = r) :
    ckPotAtK k M Δ hΔ0 hΔ C₀ (l ++ [r]) x - ckPotAtK k M Δ hΔ0 hΔ C₀ l x
      = @workFnU k (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ) (fun i => Sum.inl (C₀ i))
          ((l ++ [r]).map Sum.inl) (fun _ => Sum.inr r)
        - @workFnU k (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ) (fun i => Sum.inl (C₀ i))
          (l.map Sum.inl) (fun _ => Sum.inr r) := by
  classical
  set last : Fin k := ⟨k - 1, by omega⟩ with hlast
  set N := M ⊕ M
  letI : MetricSpace N := antipodalExtension M Δ hΔ0 hΔ
  have hk0 : 0 < k := hk
  have hmap : ((l ++ [r]).map (Sum.inl : M → N)) = (l.map Sum.inl) ++ [Sum.inl r] := by
    simp
  -- the base configuration and all but the last anchor configuration contain `Sum.inl r`
  have hbase : @workFnU k N _ (fun i => Sum.inl (C₀ i)) ((l ++ [r]).map Sum.inl)
        (fun j => Sum.inl (x j))
      = @workFnU k N _ (fun i => Sum.inl (C₀ i)) (l.map Sum.inl) (fun j => Sum.inl (x j)) := by
    rw [hmap]
    exact CKB.workFnU_snoc_of_mem hk0 _ _ _ _ ⟨last, by rw [hx]⟩
  have hmid : ∀ i : Fin k, (i : ℕ) < k - 1 →
      @workFnU k N _ (fun i => Sum.inl (C₀ i)) ((l ++ [r]).map Sum.inl) (ckConfigK x i)
        = @workFnU k N _ (fun i => Sum.inl (C₀ i)) (l.map Sum.inl) (ckConfigK x i) := by
    intro i hi
    rw [hmap]
    refine CKB.workFnU_snoc_of_mem hk0 _ _ _ _ ⟨last, ?_⟩
    have : ¬ ((last : ℕ) ≤ (i : ℕ)) := by simp only [hlast]; omega
    simp only [ckConfigK, this, if_false]
    rw [hx]
  -- the last anchor configuration is the coalesced antipode
  have hlastcfg : ckConfigK x last = (fun _ : Fin k => (Sum.inr r : N)) := by
    funext j
    have hj : (j : ℕ) ≤ (last : ℕ) := by
      have := j.isLt
      simp only [hlast]
      omega
    simp only [ckConfigK, hj, if_true]
    rw [hx]
  -- split the sums
  have hsplit : ∀ τ : List M,
      (∑ i : Fin k, @workFnU k N _ (fun i => Sum.inl (C₀ i)) (τ.map Sum.inl) (ckConfigK x i))
        = (∑ i ∈ Finset.univ.erase last,
            @workFnU k N _ (fun i => Sum.inl (C₀ i)) (τ.map Sum.inl) (ckConfigK x i))
          + @workFnU k N _ (fun i => Sum.inl (C₀ i)) (τ.map Sum.inl) (ckConfigK x last) := by
    intro τ
    rw [Finset.sum_erase_add _ _ (Finset.mem_univ last)]
  have herase : ∀ i ∈ Finset.univ.erase last, (i : ℕ) < k - 1 := by
    intro i hi
    have hne : i ≠ last := (Finset.mem_erase.mp hi).1
    have := i.isLt
    have : (i : ℕ) ≠ k - 1 := by
      intro h
      exact hne (by apply Fin.ext; simp only [hlast]; omega)
    omega
  simp only [ckPotAtK, hsplit, hbase, hlastcfg]
  have hsum : (∑ i ∈ Finset.univ.erase last,
        @workFnU k N _ (fun i => Sum.inl (C₀ i)) ((l ++ [r]).map Sum.inl) (ckConfigK x i))
      = (∑ i ∈ Finset.univ.erase last,
        @workFnU k N _ (fun i => Sum.inl (C₀ i)) (l.map Sum.inl) (ckConfigK x i)) :=
    Finset.sum_congr rfl (fun i hi => hmid i (herase i hi))
  rw [hsum]
  ring

