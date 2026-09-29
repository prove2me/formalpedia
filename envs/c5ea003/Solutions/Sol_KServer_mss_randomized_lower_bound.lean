-- Prove2me | solution 1 for KServer.mss_randomized_lower_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-04T22:45:01.425594+00:00
-- url     : https://prove2.me/submissions/2750848f-f9fe-423f-8f7d-5c961b5a03d2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_KServer_model
import Definitions.Def_KServer_evader
import Definitions.Def_KServer_evader_bail
import Definitions.Def_KServer_chunk_system_b
import Theorems.Thm_KServer_bcr_hard_chunk_system

/-!
# Theorem 11 of Bubeck–Coester–Rabani from its chunk-system form

This file derives the distributional `Ω(log² k)` lower bound for small set chasing
on `k+1` points from the existence of a hard chunk system
(`KServer.bcr_hard_chunk_system`, the chunk-system form of BCR's Lemma 12), by the
repetition argument of the paper's "Proof of Theorem 11".
-/

namespace MSSLB

open KServer

section Generic

variable {X : Type*} [MetricSpace X]

/-- Restriction of an evader algorithm to the future after a fixed history. -/
def restrict (E : EvaderAlgorithm X) (h : List (Set X)) : EvaderAlgorithm X where
  pos l := E.pos (h ++ l)
  serves l S hS := by
    have hh : h ++ (l ++ [S]) = (h ++ l) ++ [S] := by simp
    show E.pos (h ++ (l ++ [S])) ∈ S
    rw [hh]
    exact E.serves _ S hS

theorem cost_nil (E : EvaderAlgorithm X) : E.cost [] = 0 := by
  simp [EvaderAlgorithm.cost]

theorem cost_nonneg (E : EvaderAlgorithm X) (σ : List (Set X)) : 0 ≤ E.cost σ :=
  Finset.sum_nonneg fun _ _ => dist_nonneg

/-- Splitting the cost of a concatenation. -/
theorem cost_append (E : EvaderAlgorithm X) (h σ : List (Set X)) :
    E.cost (h ++ σ) = E.cost h + (restrict E h).cost σ := by
  unfold EvaderAlgorithm.cost
  have hlen : (h ++ σ).length = h.length + σ.length := by simp
  rw [hlen, Finset.sum_range_add]
  congr 1
  · refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : j < h.length := Finset.mem_range.mp hj
    have e1 : (h ++ σ).take j = h.take j := by
      rw [List.take_append]
      have : j - h.length = 0 := by omega
      rw [this]
      simp
    have e2 : (h ++ σ).take (j + 1) = h.take (j + 1) := by
      rw [List.take_append]
      have : j + 1 - h.length = 0 := by omega
      rw [this]
      simp
    rw [e1, e2]
  · refine Finset.sum_congr rfl fun i _ => ?_
    have e1 : (h ++ σ).take (h.length + i) = h ++ σ.take i := by
      rw [List.take_append]
      simp
    have e2 : (h ++ σ).take (h.length + i + 1) = h ++ σ.take (i + 1) := by
      rw [List.take_append]
      have hh : h.length + i + 1 - h.length = i + 1 := by omega
      rw [hh]
      have : (h.length + i + 1) = h.length + (i+1) := by omega
      rw [this]
      simp
    rw [e1, e2]
    rfl

theorem costOn_eq (E : EvaderAlgorithm X) (h σ : List (Set X)) :
    E.costOn h σ = (restrict E h).cost σ := by
  simp [EvaderAlgorithm.costOn, cost_append]

theorem costOn_nonneg (E : EvaderAlgorithm X) (h σ : List (Set X)) :
    0 ≤ E.costOn h σ := by
  rw [costOn_eq]; exact cost_nonneg _ _

theorem cost_mono_append (E : EvaderAlgorithm X) (h σ : List (Set X)) :
    E.cost h ≤ E.cost (h ++ σ) := by
  rw [cost_append]
  linarith [cost_nonneg (restrict E h) σ]

/-- With the never-bailing rule, the bail cost is the plain partial cost. -/
theorem bailCost_false (E : EvaderAlgorithm X) (h χ : List (Set X)) (p : ℝ) :
    E.bailCost (fun _ => false) h χ p = E.costOn h χ := by
  unfold EvaderAlgorithm.bailCost bailTime
  have : List.find? (fun _ => false) (List.range χ.length) = none := by
    apply List.find?_eq_none.mpr
    intro x _
    simp
  rw [this]

omit [MetricSpace X] in
/-- Flattening the first `i+1` entries of a list of chunks. -/
theorem flatten_take_succ {m : ℕ} (f : Fin m → List (Set X)) (i : ℕ) (hi : i < m) :
    (((List.ofFn f).take (i + 1)).flatten)
      = ((List.ofFn f).take i).flatten ++ f ⟨i, hi⟩ := by
  have hlen : (List.ofFn f).length = m := by simp
  have h1 : (List.ofFn f).take (i + 1)
      = (List.ofFn f).take i ++ [(List.ofFn f)[i]] := by
    rw [List.take_add_one]
    congr 1
    rw [List.getElem?_eq_getElem (by omega)]
    rfl
  rw [h1]
  simp

/-- Telescoping the per-chunk partial costs. -/
theorem telescope (E : EvaderAlgorithm X) {m : ℕ} (f : Fin m → List (Set X)) :
    ∑ i : Fin m, E.costOn (((List.ofFn f).take (i : ℕ)).flatten) (f i)
      = E.cost ((List.ofFn f).flatten) := by
  set g : ℕ → ℝ := fun n => E.cost (((List.ofFn f).take n).flatten) with hg
  have key : ∀ i : Fin m,
      E.costOn (((List.ofFn f).take (i : ℕ)).flatten) (f i) = g (i + 1) - g i := by
    intro i
    have hfl := flatten_take_succ f (i : ℕ) i.isLt
    simp only [EvaderAlgorithm.costOn, hg]
    rw [hfl]
  rw [Finset.sum_congr rfl (fun i _ => key i)]
  have : ∑ i : Fin m, (g ((i : ℕ) + 1) - g (i : ℕ))
      = ∑ i ∈ Finset.range m, (g (i + 1) - g i) :=
    Fin.sum_univ_eq_sum_range (fun i => g (i + 1) - g i) m
  rw [this, Finset.sum_range_sub g m]
  have h0 : g 0 = 0 := by simp [hg, cost_nil]
  have hm : g m = E.cost ((List.ofFn f).flatten) := by
    have htake : (List.ofFn f).take m = List.ofFn f :=
      List.take_of_length_le (by simp)
    simp only [hg, htake]
  rw [h0, hm, sub_zero]

/-! ### Offline cost -/

/-- The set whose infimum defines the offline cost. -/
theorem offline_set_nonempty (x : X) (σ : List (Set X)) :
    ∃ P : ℕ → X, EvaderServes x σ P := by
  classical
  set pick : Set X → X := fun S => if h : S.Nonempty then h.choose else x with hpick
  have hpick_mem : ∀ S : Set X, S.Nonempty → pick S ∈ S := by
    intro S hS
    simp only [hpick, dif_pos hS]
    exact hS.choose_spec
  refine ⟨fun j => if hj : 0 < j ∧ j - 1 < σ.length then pick (σ.get ⟨j - 1, hj.2⟩)
      else x, ?_, ?_⟩
  · simp
  · intro j hj
    have h1 : 0 < (j : ℕ) + 1 ∧ ((j : ℕ) + 1) - 1 < σ.length := ⟨Nat.succ_pos _, by simp⟩
    simp only [dif_pos h1]
    have h2 : (⟨((j : ℕ) + 1) - 1, h1.2⟩ : Fin σ.length) = j := by
      apply Fin.ext; simp
    rw [h2]
    exact hpick_mem _ hj

theorem offline_nonneg (x : X) (σ : List (Set X)) : 0 ≤ evaderOfflineCost x σ := by
  obtain ⟨P, hP⟩ := offline_set_nonempty x σ
  refine le_csInf ⟨∑ j ∈ Finset.range σ.length, dist (P j) (P (j + 1)),
    ⟨P, hP, rfl⟩⟩ ?_
  rintro b ⟨Q, _, rfl⟩
  exact Finset.sum_nonneg fun _ _ => dist_nonneg

theorem offline_bddBelow (x : X) (σ : List (Set X)) :
    BddBelow {c : ℝ | ∃ P : ℕ → X, EvaderServes x σ P ∧
      c = ∑ j ∈ Finset.range σ.length, dist (P j) (P (j + 1))} := by
  refine ⟨0, ?_⟩
  rintro b ⟨Q, _, rfl⟩
  exact Finset.sum_nonneg fun _ _ => dist_nonneg

/-- A serving path witnesses an upper bound on the offline cost. -/
theorem offline_le_of_serves {x : X} {σ : List (Set X)} {P : ℕ → X}
    (hP : EvaderServes x σ P) :
    evaderOfflineCost x σ ≤ ∑ j ∈ Finset.range σ.length, dist (P j) (P (j + 1)) :=
  csInf_le (offline_bddBelow x σ) ⟨P, hP, rfl⟩

/-- If every serving path costs at least `r`, then so does the offline optimum. -/
theorem le_offline {x : X} {σ : List (Set X)} {r : ℝ}
    (h : ∀ P : ℕ → X, EvaderServes x σ P →
      r ≤ ∑ j ∈ Finset.range σ.length, dist (P j) (P (j + 1))) :
    r ≤ evaderOfflineCost x σ := by
  obtain ⟨P, hP⟩ := offline_set_nonempty x σ
  refine le_csInf ⟨∑ j ∈ Finset.range σ.length, dist (P j) (P (j + 1)),
    ⟨P, hP, rfl⟩⟩ ?_
  rintro b ⟨Q, hQ, rfl⟩
  exact h Q hQ

/-- Moving the starting point costs at most the distance. -/
theorem offline_shift (x y : X) (σ : List (Set X)) :
    evaderOfflineCost x σ ≤ dist x y + evaderOfflineCost y σ := by
  classical
  have hkey : ∀ b ∈ {c : ℝ | ∃ P : ℕ → X, EvaderServes y σ P ∧
      c = ∑ j ∈ Finset.range σ.length, dist (P j) (P (j + 1))},
      evaderOfflineCost x σ ≤ dist x y + b := by
    rintro b ⟨Q, hQ, rfl⟩
    set P : ℕ → X := fun j => if j = 0 then x else Q j with hP
    have hserves : EvaderServes x σ P := by
      refine ⟨by simp [hP], ?_⟩
      intro j hj
      have : P ((j : ℕ) + 1) = Q ((j : ℕ) + 1) := by simp [hP]
      rw [this]
      exact hQ.2 j hj
    refine le_trans (offline_le_of_serves hserves) ?_
    rcases hL : σ.length with _ | nn
    · simp only [Finset.range_zero, Finset.sum_empty]
      have h4 : (0:ℝ) ≤ dist x y := dist_nonneg
      have h5 : (0:ℝ) ≤ ∑ j ∈ Finset.range 0, dist (Q j) (Q (j + 1)) :=
        Finset.sum_nonneg fun _ _ => dist_nonneg
      simp only [Finset.range_zero, Finset.sum_empty] at h5
      linarith
    · rw [Finset.sum_range_succ' (fun j => dist (P j) (P (j + 1))) nn,
        Finset.sum_range_succ' (fun j => dist (Q j) (Q (j + 1))) nn]
      have h1 : ∑ i ∈ Finset.range nn, dist (P (i + 1)) (P (i + 1 + 1))
          = ∑ i ∈ Finset.range nn, dist (Q (i + 1)) (Q (i + 1 + 1)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        have e1 : P (i + 1) = Q (i + 1) := by simp [hP]
        have e2 : P (i + 1 + 1) = Q (i + 1 + 1) := by simp [hP]
        rw [e1, e2]
      have h2 : dist (P 0) (P (0 + 1)) ≤ dist x y + dist (Q 0) (Q (0 + 1)) := by
        have hP0 : P 0 = x := by simp [hP]
        have hP1 : P (0 + 1) = Q (0 + 1) := by simp [hP]
        rw [hP0, hP1, hQ.1]
        exact dist_triangle x y (Q (0 + 1))
      rw [h1]
      linarith
  have hb : BddBelow {c : ℝ | ∃ P : ℕ → X, EvaderServes y σ P ∧
      c = ∑ j ∈ Finset.range σ.length, dist (P j) (P (j + 1))} := offline_bddBelow y σ
  obtain ⟨P₀, hP₀⟩ := offline_set_nonempty y σ
  have hne : Set.Nonempty {c : ℝ | ∃ P : ℕ → X, EvaderServes y σ P ∧
      c = ∑ j ∈ Finset.range σ.length, dist (P j) (P (j + 1))} := ⟨_, ⟨P₀, hP₀, rfl⟩⟩
  have : evaderOfflineCost x σ - dist x y ≤ evaderOfflineCost y σ := by
    apply le_csInf hne
    intro b hbmem
    have := hkey b hbmem
    linarith
  linarith

/-- Any path serving a list whose last request is `{y}` ends at `y`. -/
theorem serves_last {x y : X} {σ : List (Set X)} {P : ℕ → X}
    (hlast : σ.getLast? = some ({y} : Set X)) (hP : EvaderServes x σ P) :
    P σ.length = y := by
  have hne : σ ≠ [] := by
    intro h
    rw [h] at hlast
    simp at hlast
  have hpos : 0 < σ.length := List.length_pos_iff.mpr hne
  have hget : σ.get ⟨σ.length - 1, by omega⟩ = ({y} : Set X) := by
    have h2 : σ[σ.length - 1]? = some ({y} : Set X) := by
      rw [← List.getLast?_eq_getElem?]; exact hlast
    rw [List.getElem?_eq_getElem (by omega)] at h2
    simpa using h2
  have h3 := hP.2 ⟨σ.length - 1, by omega⟩ (by rw [hget]; exact ⟨y, rfl⟩)
  rw [hget] at h3
  have : (σ.length - 1) + 1 = σ.length := by omega
  rw [this] at h3
  simpa using h3

/-- Concatenation, when the first part ends with a singleton request. -/
theorem offline_append_last {x y : X} {σ₁ σ₂ : List (Set X)}
    (hlast : σ₁.getLast? = some ({y} : Set X)) :
    evaderOfflineCost x (σ₁ ++ σ₂)
      ≤ evaderOfflineCost x σ₁ + evaderOfflineCost y σ₂ := by
  classical
  have main : ∀ b₁ ∈ {c : ℝ | ∃ P : ℕ → X, EvaderServes x σ₁ P ∧
        c = ∑ j ∈ Finset.range σ₁.length, dist (P j) (P (j + 1))},
      ∀ b₂ ∈ {c : ℝ | ∃ P : ℕ → X, EvaderServes y σ₂ P ∧
        c = ∑ j ∈ Finset.range σ₂.length, dist (P j) (P (j + 1))},
      evaderOfflineCost x (σ₁ ++ σ₂) ≤ b₁ + b₂ := by
    rintro b₁ ⟨P, hP, rfl⟩ b₂ ⟨Q, hQ, rfl⟩
    have hPend : P σ₁.length = y := serves_last hlast hP
    set R : ℕ → X := fun j => if j ≤ σ₁.length then P j else Q (j - σ₁.length) with hR
    have hRserves : EvaderServes x (σ₁ ++ σ₂) R := by
      constructor
      · simp [hR, hP.1]
      · intro j hj
        by_cases hcase : (j : ℕ) < σ₁.length
        · have hget : (σ₁ ++ σ₂).get j = σ₁.get ⟨j, hcase⟩ := by
            simp [List.getElem_append_left hcase]
          have hjne : (σ₁.get ⟨j, hcase⟩).Nonempty := by rw [← hget]; exact hj
          have hRj : R ((j : ℕ) + 1) = P ((j : ℕ) + 1) := by
            simp only [hR]
            rw [if_pos (by omega)]
          rw [hget, hRj]
          exact hP.2 ⟨j, hcase⟩ hjne
        · have hjlt : (j : ℕ) < σ₁.length + σ₂.length := by
            have := j.isLt; simpa using this
          have hge : σ₁.length ≤ (j : ℕ) := by omega
          have hidx : (j : ℕ) - σ₁.length < σ₂.length := by omega
          have hget : (σ₁ ++ σ₂).get j = σ₂.get ⟨(j : ℕ) - σ₁.length, hidx⟩ := by
            simp [List.getElem_append_right hge]
          have hjne : (σ₂.get ⟨(j : ℕ) - σ₁.length, hidx⟩).Nonempty := by
            rw [← hget]; exact hj
          have hRj : R ((j : ℕ) + 1) = Q ((j : ℕ) + 1 - σ₁.length) := by
            simp only [hR]
            rw [if_neg (by omega)]
          rw [hget, hRj]
          have hidx2 : (j : ℕ) + 1 - σ₁.length = ((j : ℕ) - σ₁.length) + 1 := by omega
          rw [hidx2]
          exact hQ.2 ⟨(j : ℕ) - σ₁.length, hidx⟩ hjne
    refine le_trans (offline_le_of_serves hRserves) ?_
    have hlen : (σ₁ ++ σ₂).length = σ₁.length + σ₂.length := by simp
    rw [hlen, Finset.sum_range_add]
    have e1 : ∑ j ∈ Finset.range σ₁.length, dist (R j) (R (j + 1))
        = ∑ j ∈ Finset.range σ₁.length, dist (P j) (P (j + 1)) := by
      refine Finset.sum_congr rfl fun j hj => ?_
      have hjlt : j < σ₁.length := Finset.mem_range.mp hj
      have a1 : R j = P j := by simp only [hR]; rw [if_pos (by omega)]
      have a2 : R (j + 1) = P (j + 1) := by simp only [hR]; rw [if_pos (by omega)]
      rw [a1, a2]
    have e2 : ∑ i ∈ Finset.range σ₂.length, dist (R (σ₁.length + i)) (R (σ₁.length + i + 1))
        = ∑ i ∈ Finset.range σ₂.length, dist (Q i) (Q (i + 1)) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      have a1 : R (σ₁.length + i) = Q i := by
        simp only [hR]
        rcases Nat.eq_zero_or_pos i with h0 | hpos
        · subst h0
          rw [if_pos (by omega)]
          simpa [hQ.1] using hPend
        · rw [if_neg (by omega)]
          congr 1
          omega
      have a2 : R (σ₁.length + i + 1) = Q (i + 1) := by
        simp only [hR]
        rw [if_neg (by omega)]
        congr 1
        omega
      rw [a1, a2]
    rw [e1, e2]
  -- now pass to infima
  obtain ⟨P₀, hP₀⟩ := offline_set_nonempty x σ₁
  obtain ⟨Q₀, hQ₀⟩ := offline_set_nonempty y σ₂
  have step1 : ∀ b₁ ∈ {c : ℝ | ∃ P : ℕ → X, EvaderServes x σ₁ P ∧
        c = ∑ j ∈ Finset.range σ₁.length, dist (P j) (P (j + 1))},
      evaderOfflineCost x (σ₁ ++ σ₂) - b₁ ≤ evaderOfflineCost y σ₂ := by
    intro b₁ hb₁
    refine le_csInf ⟨∑ j ∈ Finset.range σ₂.length, dist (Q₀ j) (Q₀ (j + 1)),
      ⟨Q₀, hQ₀, rfl⟩⟩ ?_
    intro b₂ hb₂
    have := main b₁ hb₁ b₂ hb₂
    linarith
  have step2 : evaderOfflineCost x (σ₁ ++ σ₂) - evaderOfflineCost y σ₂
      ≤ evaderOfflineCost x σ₁ := by
    refine le_csInf ⟨∑ j ∈ Finset.range σ₁.length, dist (P₀ j) (P₀ (j + 1)),
      ⟨P₀, hP₀, rfl⟩⟩ ?_
    intro b₁ hb₁
    have := step1 b₁ hb₁
    linarith
  linarith

/-- The length of a path between two indices dominates the distance. -/
theorem dist_le_path_sum (P : ℕ → X) (a b : ℕ) (hab : a ≤ b) :
    dist (P a) (P b) ≤ ∑ j ∈ Finset.Ico a b, dist (P j) (P (j + 1)) := by
  induction b with
  | zero =>
    have : a = 0 := Nat.le_zero.mp hab
    subst this
    simp
  | succ n ih =>
    rcases Nat.lt_or_ge a (n + 1) with h | h
    · have han : a ≤ n := by omega
      have hsum : ∑ j ∈ Finset.Ico a (n + 1), dist (P j) (P (j + 1))
          = (∑ j ∈ Finset.Ico a n, dist (P j) (P (j + 1))) + dist (P n) (P (n + 1)) := by
        rw [Finset.sum_Ico_succ_top han]
      rw [hsum]
      have := ih han
      have htri := dist_triangle (P a) (P n) (P (n + 1))
      linarith
    · have : a = n + 1 := by omega
      subst this
      simp

end Generic

/-! ### The expected cost of a chunk system -/

section System

variable {X : Type*} [MetricSpace X] {s t : X} {cHi T price : ℝ} {M : ℕ}

/-- Every evader pays at least the system's expected total, in expectation. -/
theorem system_cost_bound (C : ChunkSystemB X s t 0 cHi T price M)
    (E : EvaderAlgorithm X) :
    T ≤ ∑ ω, C.P ω * E.cost (C.seq ω) := by
  classical
  have hfib : ∀ (i : ℕ) (v : C.Ω → ℝ),
      ∑ b ∈ Finset.univ.image (C.hist i),
        ∑ ω ∈ Finset.univ.filter (fun ω => C.hist i ω = b), v ω
      = ∑ ω, v ω := fun i v =>
    Finset.sum_fiberwise_of_maps_to
      (fun x _ => Finset.mem_image_of_mem _ (Finset.mem_univ x)) v
  have step : ∀ i : Fin C.m, ∑ ω, C.P ω * C.size ω i
      ≤ ∑ ω, C.P ω * E.costOn (((List.ofFn (C.chunk ω)).take (i : ℕ)).flatten)
          (C.chunk ω i) := by
    intro i
    rw [← hfib (i : ℕ) (fun ω => C.P ω * C.size ω i),
      ← hfib (i : ℕ) (fun ω => C.P ω * E.costOn
        (((List.ofFn (C.chunk ω)).take (i : ℕ)).flatten) (C.chunk ω i))]
    refine Finset.sum_le_sum fun b hb => ?_
    rw [Finset.mem_image] at hb
    obtain ⟨ω₀, -, rfl⟩ := hb
    have hc := C.hcost i ω₀ E (fun _ => false)
    simp only [bailCost_false] at hc
    have hleft : ∑ ω ∈ Finset.univ.filter (fun ω => C.hist (i : ℕ) ω = C.hist (i : ℕ) ω₀),
        C.P ω * C.size ω i
        = C.size ω₀ i * ∑ ω ∈ Finset.univ.filter
            (fun ω => C.hist (i : ℕ) ω = C.hist (i : ℕ) ω₀), C.P ω := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun ω hω => ?_
      have hmem : C.hist (i : ℕ) ω = C.hist (i : ℕ) ω₀ := by
        simpa using (Finset.mem_filter.mp hω).2
      rw [C.hsmeas i ω ω₀ hmem]
      ring
    rw [hleft]
    exact hc
  have h2 : ∑ ω, C.P ω * ∑ i, C.size ω i = ∑ i : Fin C.m, ∑ ω, C.P ω * C.size ω i := by
    have hmul : ∀ ω : C.Ω, C.P ω * ∑ i, C.size ω i = ∑ i, C.P ω * C.size ω i :=
      fun ω => Finset.mul_sum _ _ _
    simp_rw [hmul]
    exact Finset.sum_comm
  have h3 : ∑ i : Fin C.m, ∑ ω, C.P ω * C.size ω i
      ≤ ∑ i : Fin C.m, ∑ ω, C.P ω * E.costOn
          (((List.ofFn (C.chunk ω)).take (i : ℕ)).flatten) (C.chunk ω i) :=
    Finset.sum_le_sum fun i _ => step i
  have h4 : ∑ i : Fin C.m, ∑ ω, C.P ω * E.costOn
        (((List.ofFn (C.chunk ω)).take (i : ℕ)).flatten) (C.chunk ω i)
      = ∑ ω, C.P ω * E.cost (C.seq ω) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ω _ => ?_
    rw [← Finset.mul_sum, telescope E (C.chunk ω)]
    rfl
  calc T ≤ ∑ ω, C.P ω * ∑ i, C.size ω i := C.htotal
    _ = ∑ i : Fin C.m, ∑ ω, C.P ω * C.size ω i := h2
    _ ≤ ∑ i : Fin C.m, ∑ ω, C.P ω * E.costOn
          (((List.ofFn (C.chunk ω)).take (i : ℕ)).flatten) (C.chunk ω i) := h3
    _ = ∑ ω, C.P ω * E.cost (C.seq ω) := h4

/-! ### Repetition -/

/-- One block: a full run of the system, followed by a request forcing a return
to the starting point `s`. -/
def blockSeq (C : ChunkSystemB X s t 0 cHi T price M) (ω : C.Ω) : List (Set X) :=
  C.seq ω ++ [{s}]

/-- The concatenation of the blocks of a list of outcomes. -/
def repSeq (C : ChunkSystemB X s t 0 cHi T price M) : List C.Ω → List (Set X)
  | [] => []
  | ω :: l => blockSeq C ω ++ repSeq C l

/-- The product weight of a tuple of outcomes. -/
noncomputable def wt (C : ChunkSystemB X s t 0 cHi T price M) {R : ℕ}
    (f : Fin R → C.Ω) : ℝ := ∏ r, C.P (f r)

variable (C : ChunkSystemB X s t 0 cHi T price M)

theorem wt_nonneg {R : ℕ} (f : Fin R → C.Ω) : 0 ≤ wt C f :=
  Finset.prod_nonneg fun r _ => le_of_lt (C.hP (f r))

theorem wt_sum_one (R : ℕ) : ∑ f : Fin R → C.Ω, wt C f = 1 := by
  classical
  have h := Finset.prod_univ_sum (fun _ : Fin R => (Finset.univ : Finset C.Ω))
    (fun (_ : Fin R) (ω : C.Ω) => C.P ω)
  simp only [C.hPsum, Finset.prod_const_one] at h
  rw [show (Fintype.piFinset fun _ : Fin R => (Finset.univ : Finset C.Ω))
      = (Finset.univ : Finset (Fin R → C.Ω)) by
    ext f; simp] at h
  exact h.symm

theorem blockSeq_getLast (ω : C.Ω) : (blockSeq C ω).getLast? = some ({s} : Set X) := by
  simp [blockSeq]

theorem repSeq_getLast : ∀ l : List C.Ω, l ≠ [] →
    (repSeq C l).getLast? = some ({s} : Set X) := by
  intro l
  induction l with
  | nil => intro h; exact absurd rfl h
  | cons ω l ih =>
    intro _
    rcases l with _ | ⟨ω', l'⟩
    · show (blockSeq C ω ++ repSeq C []).getLast? = _
      simp [repSeq, blockSeq]
    · show (blockSeq C ω ++ repSeq C (ω' :: l')).getLast? = _
      rw [List.getLast?_append_of_ne_nil]
      · exact ih (by simp)
      · show repSeq C (ω' :: l') ≠ []
        show blockSeq C ω' ++ repSeq C l' ≠ []
        simp [blockSeq]

theorem repSeq_nonempty_sets : ∀ (l : List C.Ω), ∀ S ∈ repSeq C l, S.Nonempty := by
  intro l
  induction l with
  | nil => intro S hS; simp [repSeq] at hS
  | cons ω l ih =>
    intro S hS
    have hS' : S ∈ blockSeq C ω ++ repSeq C l := hS
    rcases List.mem_append.mp hS' with h | h
    · rcases List.mem_append.mp h with h1 | h1
      · obtain ⟨χ, hχ, hSχ⟩ := List.mem_flatten.mp h1
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hχ
        exact C.hne ω i S hSχ
      · have : S = ({s} : Set X) := by simpa using h1
        exact this ▸ ⟨s, rfl⟩
    · exact ih S h

/-- The offline cost of one block, started at `s`. -/
theorem block_offline_le (ω : C.Ω) :
    evaderOfflineCost s (blockSeq C ω) ≤ 2 * dist s t := by
  have h1 : evaderOfflineCost s (blockSeq C ω)
      ≤ evaderOfflineCost s (C.seq ω) + evaderOfflineCost t ([{s}] : List (Set X)) :=
    offline_append_last (by
      have := C.hlast ω
      simpa [ChunkSystemB.seq] using this)
  have h2 : evaderOfflineCost s (C.seq ω) ≤ dist s t := C.hopt ω
  have h3 : evaderOfflineCost t ([{s}] : List (Set X)) ≤ dist s t := by
    have hserves : EvaderServes t ([{s}] : List (Set X)) (fun j => if j = 0 then t else s) := by
      refine ⟨by simp, ?_⟩
      intro j _
      simp
    have := offline_le_of_serves hserves
    simpa [dist_comm] using this
  linarith

/-- The offline cost of a repeated instance, started at `s`. -/
theorem rep_offline_le : ∀ l : List C.Ω,
    evaderOfflineCost s (repSeq C l) ≤ (l.length : ℝ) * (2 * dist s t) := by
  intro l
  induction l with
  | nil =>
    have hserves : EvaderServes s ([] : List (Set X)) (fun _ => s) := ⟨rfl, by intro j; exact absurd j.isLt (by simp)⟩
    have := offline_le_of_serves hserves
    simpa [repSeq] using this
  | cons ω l ih =>
    have hsplit : evaderOfflineCost s (repSeq C (ω :: l))
        ≤ evaderOfflineCost s (blockSeq C ω) + evaderOfflineCost s (repSeq C l) :=
      offline_append_last (blockSeq_getLast C ω)
    have hb := block_offline_le C ω
    have hlen : ((ω :: l).length : ℝ) = (l.length : ℝ) + 1 := by
      rw [List.length_cons]; push_cast; ring
    rw [hlen]
    linarith

/-- Serving a concatenation restricts to serving the first part. -/
theorem serves_prefix {x : X} {σ₁ σ₂ : List (Set X)} {P : ℕ → X}
    (hP : EvaderServes x (σ₁ ++ σ₂) P) : EvaderServes x σ₁ P := by
  refine ⟨hP.1, ?_⟩
  intro j hj
  have hjlt : (j : ℕ) < (σ₁ ++ σ₂).length := by
    have hj2 := j.isLt
    simp only [List.length_append]
    omega
  have hget : (σ₁ ++ σ₂).get ⟨j, hjlt⟩ = σ₁.get j := by
    simp [List.getElem_append_left j.isLt]
  have := hP.2 ⟨j, hjlt⟩ (by rw [hget]; exact hj)
  rw [hget] at this
  exact this

/-- Serving a concatenation restricts to serving the second part from the
intermediate position. -/
theorem serves_suffix {x : X} {σ₁ σ₂ : List (Set X)} {P : ℕ → X}
    (hP : EvaderServes x (σ₁ ++ σ₂) P) :
    EvaderServes (P σ₁.length) σ₂ (fun j => P (σ₁.length + j)) := by
  refine ⟨by simp, ?_⟩
  intro j hj
  have hjlt : σ₁.length + (j : ℕ) < (σ₁ ++ σ₂).length := by
    have hj2 := j.isLt
    simp only [List.length_append]
    omega
  have hget : (σ₁ ++ σ₂).get ⟨σ₁.length + (j : ℕ), hjlt⟩ = σ₂.get j := by
    simp [List.getElem_append_right]
  have h := hP.2 ⟨σ₁.length + (j : ℕ), hjlt⟩ (by rw [hget]; exact hj)
  rw [hget] at h
  have he : σ₁.length + ((j : ℕ) + 1) = σ₁.length + (j : ℕ) + 1 := by omega
  show P (σ₁.length + ((j : ℕ) + 1)) ∈ _
  rw [he]
  exact h

/-- Every path serving a repeated instance is long. -/
theorem rep_path_lower : ∀ (l : List C.Ω) (x : X) (P : ℕ → X),
    EvaderServes x (repSeq C l) P →
      (l.length : ℝ) * dist s t
        ≤ ∑ j ∈ Finset.range (repSeq C l).length, dist (P j) (P (j + 1)) := by
  intro l
  induction l with
  | nil =>
    intro x P _
    simp [repSeq]
  | cons ω l ih =>
    intro x P hP
    have hPc : EvaderServes x (blockSeq C ω ++ repSeq C l) P := hP
    set L₁ := (blockSeq C ω).length with hL₁
    set L₂ := (repSeq C l).length with hL₂
    have hlen : (repSeq C (ω :: l)).length = L₁ + L₂ := by
      show (blockSeq C ω ++ repSeq C l).length = L₁ + L₂
      simp [hL₁, hL₂]
    rw [hlen, Finset.sum_range_add]
    -- the first block costs at least `dist s t`
    have hpre : EvaderServes x (blockSeq C ω) P := serves_prefix hPc
    have hPs : P L₁ = s := serves_last (blockSeq_getLast C ω) hpre
    have hpre2 : EvaderServes x (C.seq ω) P := serves_prefix (σ₂ := [{s}]) hpre
    have hPt : P (C.seq ω).length = t :=
      serves_last (by simpa [ChunkSystemB.seq] using C.hlast ω) hpre2
    have hle : (C.seq ω).length ≤ L₁ := by
      simp [hL₁, blockSeq]
    have hfirst : dist s t ≤ ∑ j ∈ Finset.range L₁, dist (P j) (P (j + 1)) := by
      have hsub : Finset.Ico (C.seq ω).length L₁ ⊆ Finset.range L₁ := by
        intro j hj
        rw [Finset.mem_Ico] at hj
        exact Finset.mem_range.mpr hj.2
      have h1 : dist (P (C.seq ω).length) (P L₁)
          ≤ ∑ j ∈ Finset.Ico (C.seq ω).length L₁, dist (P j) (P (j + 1)) :=
        dist_le_path_sum P _ _ hle
      have h2 : ∑ j ∈ Finset.Ico (C.seq ω).length L₁, dist (P j) (P (j + 1))
          ≤ ∑ j ∈ Finset.range L₁, dist (P j) (P (j + 1)) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => dist_nonneg)
      rw [hPt, hPs] at h1
      rw [dist_comm] at h1
      linarith
    -- the rest, by induction
    have hsuf : EvaderServes (P L₁) (repSeq C l) (fun j => P (L₁ + j)) := by
      have := serves_suffix (σ₁ := blockSeq C ω) (σ₂ := repSeq C l) hPc
      simpa [hL₁] using this
    have hrest := ih (P L₁) (fun j => P (L₁ + j)) hsuf
    have hrest' : (l.length : ℝ) * dist s t
        ≤ ∑ i ∈ Finset.range L₂, dist (P (L₁ + i)) (P (L₁ + i + 1)) := by
      refine le_trans hrest (le_of_eq ?_)
      refine Finset.sum_congr rfl fun i _ => ?_
      have : L₁ + (i + 1) = L₁ + i + 1 := by omega
      simp [this]
    have hlen2 : ((ω :: l).length : ℝ) = (l.length : ℝ) + 1 := by
      rw [List.length_cons]; push_cast; ring
    rw [hlen2]
    have : dist s t + (l.length : ℝ) * dist s t
        ≤ (∑ j ∈ Finset.range L₁, dist (P j) (P (j + 1)))
          + ∑ i ∈ Finset.range L₂, dist (P (L₁ + i)) (P (L₁ + i + 1)) := by
      linarith
    linarith

/-- The offline optimum of a repeated instance is large, from every start. -/
theorem rep_offline_ge (l : List C.Ω) (x : X) :
    (l.length : ℝ) * dist s t ≤ evaderOfflineCost x (repSeq C l) :=
  le_offline (fun P hP => rep_path_lower C l x P hP)

/-- The expected online cost of a repeated instance. -/
theorem rep_cost_bound : ∀ (R : ℕ) (E : EvaderAlgorithm X),
    (R : ℝ) * T ≤ ∑ f : Fin R → C.Ω, wt C f * E.cost (repSeq C (List.ofFn f)) := by
  intro R
  induction R with
  | zero =>
    intro E
    have : ∀ f : Fin 0 → C.Ω, wt C f * E.cost (repSeq C (List.ofFn f)) = 0 := by
      intro f
      simp [wt, repSeq, cost_nil]
    rw [Finset.sum_congr rfl (fun f _ => this f)]
    simp
  | succ R ih =>
    intro E
    classical
    let e : C.Ω × (Fin R → C.Ω) ≃ (Fin (R + 1) → C.Ω) :=
      { toFun := fun q => Fin.cons q.1 q.2
        invFun := fun f => (f 0, fun i => f i.succ)
        left_inv := by rintro ⟨a, g⟩; simp
        right_inv := by
          intro f
          funext i
          refine Fin.cases ?_ ?_ i <;> simp }
    have hsum : ∑ f : Fin (R + 1) → C.Ω, wt C f * E.cost (repSeq C (List.ofFn f))
        = ∑ q : C.Ω × (Fin R → C.Ω),
            wt C (e q) * E.cost (repSeq C (List.ofFn (e q))) :=
      (Equiv.sum_comp e (fun f => wt C f * E.cost (repSeq C (List.ofFn f)))).symm
    have hcons : ∀ (ω : C.Ω) (g : Fin R → C.Ω),
        wt C (Fin.cons ω g : Fin (R+1) → C.Ω) = C.P ω * wt C g := by
      intro ω g
      simp [wt, Fin.prod_univ_succ]
    have hlist : ∀ (ω : C.Ω) (g : Fin R → C.Ω),
        List.ofFn (Fin.cons ω g : Fin (R+1) → C.Ω) = ω :: List.ofFn g := by
      intro ω g
      rw [List.ofFn_succ]
      simp
    have hexp : ∑ q : C.Ω × (Fin R → C.Ω),
          wt C (e q) * E.cost (repSeq C (List.ofFn (e q)))
        = ∑ ω : C.Ω, ∑ g : Fin R → C.Ω,
            (C.P ω * wt C g) * (E.cost (blockSeq C ω)
              + (restrict E (blockSeq C ω)).cost (repSeq C (List.ofFn g))) := by
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun ω _ => ?_
      refine Finset.sum_congr rfl fun g _ => ?_
      have h1 : (e (ω, g)) = (Fin.cons ω g : Fin (R+1) → C.Ω) := rfl
      rw [h1, hcons, hlist]
      congr 1
      show E.cost (blockSeq C ω ++ repSeq C (List.ofFn g)) = _
      rw [cost_append]
    rw [hsum, hexp]
    have hsplit : ∀ ω : C.Ω, ∑ g : Fin R → C.Ω,
          (C.P ω * wt C g) * (E.cost (blockSeq C ω)
            + (restrict E (blockSeq C ω)).cost (repSeq C (List.ofFn g)))
        = C.P ω * E.cost (blockSeq C ω)
          + C.P ω * ∑ g : Fin R → C.Ω,
              wt C g * (restrict E (blockSeq C ω)).cost (repSeq C (List.ofFn g)) := by
      intro ω
      have hexpand : ∀ g : Fin R → C.Ω,
          (C.P ω * wt C g) * (E.cost (blockSeq C ω)
            + (restrict E (blockSeq C ω)).cost (repSeq C (List.ofFn g)))
          = C.P ω * E.cost (blockSeq C ω) * wt C g
            + C.P ω * (wt C g * (restrict E (blockSeq C ω)).cost
                (repSeq C (List.ofFn g))) := by
        intro g; ring
      rw [Finset.sum_congr rfl (fun g _ => hexpand g), Finset.sum_add_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum, wt_sum_one C R, mul_one]
    rw [Finset.sum_congr rfl (fun ω _ => hsplit ω), Finset.sum_add_distrib]
    have hA : T ≤ ∑ ω, C.P ω * E.cost (blockSeq C ω) := by
      refine le_trans (system_cost_bound C E) ?_
      refine Finset.sum_le_sum fun ω _ => ?_
      have := cost_mono_append E (C.seq ω) [{s}]
      have hPpos := le_of_lt (C.hP ω)
      have : E.cost (C.seq ω) ≤ E.cost (blockSeq C ω) := this
      nlinarith [this, hPpos]
    have hB : (R : ℝ) * T ≤ ∑ ω : C.Ω, C.P ω * ∑ g : Fin R → C.Ω,
        wt C g * (restrict E (blockSeq C ω)).cost (repSeq C (List.ofFn g)) := by
      have hterm : ∀ ω : C.Ω, C.P ω * ((R : ℝ) * T)
          ≤ C.P ω * ∑ g : Fin R → C.Ω,
              wt C g * (restrict E (blockSeq C ω)).cost (repSeq C (List.ofFn g)) := by
        intro ω
        exact mul_le_mul_of_nonneg_left (ih (restrict E (blockSeq C ω)))
          (le_of_lt (C.hP ω))
      have hsum2 : ∑ ω : C.Ω, C.P ω * ((R : ℝ) * T) = (R : ℝ) * T := by
        rw [← Finset.sum_mul, C.hPsum, one_mul]
      calc (R : ℝ) * T = ∑ ω : C.Ω, C.P ω * ((R : ℝ) * T) := hsum2.symm
        _ ≤ _ := Finset.sum_le_sum fun ω _ => hterm ω
    have hcast : ((R + 1 : ℕ) : ℝ) * T = T + (R : ℝ) * T := by push_cast; ring
    rw [hcast]
    linarith

end System

end MSSLB

theorem solution :
    ∃ c : ℝ, 0 < c ∧ ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      ∃ m : MetricSpace (Fin (k + 1)),
        ∀ N : ℝ, ∃ (n : ℕ) (p : Fin n → ℝ) (σ : Fin n → List (Set (Fin (k + 1)))),
          (∀ j, 0 ≤ p j) ∧ (∑ j, p j) = 1 ∧
          (∀ j, ∀ S ∈ σ j, S.Nonempty) ∧
          (∀ x₀ : Fin (k + 1),
            N ≤ ∑ j, p j * @KServer.evaderOfflineCost (Fin (k + 1)) m x₀ (σ j)) ∧
          (∀ E : @KServer.EvaderAlgorithm (Fin (k + 1)) m,
            c * Real.log k ^ 2
                * ∑ j, p j * @KServer.evaderOfflineCost (Fin (k + 1)) m
                    (@KServer.EvaderAlgorithm.pos (Fin (k + 1)) m E []) (σ j)
              ≤ ∑ j, p j * @KServer.EvaderAlgorithm.cost (Fin (k + 1)) m E (σ j)) := by
  classical
  obtain ⟨c₁, hc₁, k₀, hk⟩ := KServer.bcr_hard_chunk_system
  refine ⟨c₁ / 3, by positivity, k₀, ?_⟩
  intro k hkk
  obtain ⟨m, s, t, cHi, T, price, M, hprice, hdpos, hTge, hCne⟩ := hk k hkk
  obtain ⟨C⟩ := hCne
  refine ⟨m, ?_⟩
  intro N
  letI : MetricSpace (Fin (k + 1)) := m
  have hd : (0 : ℝ) < dist s t := hdpos
  obtain ⟨Δ, hΔ⟩ : ∃ Δ : ℝ, ∀ x : Fin (k + 1), dist x s ≤ Δ :=
    ⟨Finset.univ.sup' ⟨s, Finset.mem_univ s⟩ (fun x : Fin (k + 1) => dist x s),
      fun x => Finset.le_sup' (fun x : Fin (k + 1) => dist x s) (Finset.mem_univ x)⟩
  obtain ⟨R, hR1, hR2⟩ : ∃ R : ℕ, N ≤ (R : ℝ) * dist s t ∧ Δ ≤ (R : ℝ) * dist s t := by
    obtain ⟨R, hR⟩ := exists_nat_ge (max (N / dist s t) (Δ / dist s t))
    exact ⟨R, (div_le_iff₀ hd).mp (le_trans (le_max_left _ _) hR),
      (div_le_iff₀ hd).mp (le_trans (le_max_right _ _) hR)⟩
  set e : Fin (Fintype.card (Fin R → C.Ω)) ≃ (Fin R → C.Ω) :=
    (Fintype.equivFin (Fin R → C.Ω)).symm with he
  refine ⟨Fintype.card (Fin R → C.Ω), fun j => MSSLB.wt C (e j),
    fun j => MSSLB.repSeq C (List.ofFn (e j)), fun j => MSSLB.wt_nonneg C (e j), ?_, ?_, ?_, ?_⟩
  · rw [Equiv.sum_comp e (fun f => MSSLB.wt C f)]
    exact MSSLB.wt_sum_one C R
  · intro j S hS
    exact MSSLB.repSeq_nonempty_sets C _ S hS
  · intro x₀
    have hsum1 : ∑ j, MSSLB.wt C (e j) = 1 := by
      rw [Equiv.sum_comp e (fun f => MSSLB.wt C f)]
      exact MSSLB.wt_sum_one C R
    have hterm : ∀ j, (R : ℝ) * dist s t
        ≤ KServer.evaderOfflineCost x₀ (MSSLB.repSeq C (List.ofFn (e j))) := by
      intro j
      have h := MSSLB.rep_offline_ge C (List.ofFn (e j)) x₀
      simpa using h
    calc N ≤ (R : ℝ) * dist s t := hR1
      _ = ∑ j, MSSLB.wt C (e j) * ((R : ℝ) * dist s t) := by
          rw [← Finset.sum_mul, hsum1, one_mul]
      _ ≤ ∑ j, MSSLB.wt C (e j)
            * KServer.evaderOfflineCost x₀ (MSSLB.repSeq C (List.ofFn (e j))) :=
          Finset.sum_le_sum fun j _ =>
            mul_le_mul_of_nonneg_left (hterm j) (MSSLB.wt_nonneg C (e j))
  · intro E
    have hsum1 : ∑ j, MSSLB.wt C (e j) = 1 := by
      rw [Equiv.sum_comp e (fun f => MSSLB.wt C f)]
      exact MSSLB.wt_sum_one C R
    have hupper : ∀ j, KServer.evaderOfflineCost (E.pos [])
        (MSSLB.repSeq C (List.ofFn (e j))) ≤ 3 * ((R : ℝ) * dist s t) := by
      intro j
      have h1 := MSSLB.offline_shift (E.pos []) s (MSSLB.repSeq C (List.ofFn (e j)))
      have h2 := MSSLB.rep_offline_le C (List.ofFn (e j))
      have h3 : ((List.ofFn (e j)).length : ℝ) = (R : ℝ) := by simp
      rw [h3] at h2
      have h4 := hΔ (E.pos [])
      linarith
    have hS : ∑ j, MSSLB.wt C (e j)
          * KServer.evaderOfflineCost (E.pos []) (MSSLB.repSeq C (List.ofFn (e j)))
        ≤ 3 * ((R : ℝ) * dist s t) := by
      calc ∑ j, MSSLB.wt C (e j)
            * KServer.evaderOfflineCost (E.pos []) (MSSLB.repSeq C (List.ofFn (e j)))
          ≤ ∑ j, MSSLB.wt C (e j) * (3 * ((R : ℝ) * dist s t)) :=
            Finset.sum_le_sum fun j _ =>
              mul_le_mul_of_nonneg_left (hupper j) (MSSLB.wt_nonneg C (e j))
        _ = 3 * ((R : ℝ) * dist s t) := by rw [← Finset.sum_mul, hsum1, one_mul]
    have hcost : (R : ℝ) * T
        ≤ ∑ j, MSSLB.wt C (e j) * E.cost (MSSLB.repSeq C (List.ofFn (e j))) := by
      have h := MSSLB.rep_cost_bound C R E
      rwa [← Equiv.sum_comp e
        (fun f => MSSLB.wt C f * E.cost (MSSLB.repSeq C (List.ofFn f)))] at h
    have hlog : (0 : ℝ) ≤ Real.log k ^ 2 := sq_nonneg _
    have hcoef : (0 : ℝ) ≤ c₁ / 3 * Real.log k ^ 2 := by positivity
    have hR0 : (0 : ℝ) ≤ (R : ℝ) := Nat.cast_nonneg R
    have hstep : c₁ / 3 * Real.log k ^ 2
        * ∑ j, MSSLB.wt C (e j)
            * KServer.evaderOfflineCost (E.pos []) (MSSLB.repSeq C (List.ofFn (e j)))
        ≤ c₁ / 3 * Real.log k ^ 2 * (3 * ((R : ℝ) * dist s t)) :=
      mul_le_mul_of_nonneg_left hS hcoef
    have hmul : (R : ℝ) * (c₁ * Real.log k ^ 2 * dist s t) ≤ (R : ℝ) * T :=
      mul_le_mul_of_nonneg_left hTge hR0
    have heq : c₁ / 3 * Real.log k ^ 2 * (3 * ((R : ℝ) * dist s t))
        = (R : ℝ) * (c₁ * Real.log k ^ 2 * dist s t) := by ring
    linarith [hstep, hmul, hcost, heq ▸ hstep]
