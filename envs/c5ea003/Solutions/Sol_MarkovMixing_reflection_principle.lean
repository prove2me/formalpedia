-- Prove2me | solution 1 for MarkovMixing.reflection_principle
-- status  : ACCEPTED   (prove)
-- author  : @MKPynnic
-- created : 2026-08-22T16:03:11.03939+00:00
-- url     : https://prove2.me/submissions/28367504-0263-4057-8690-16f4118ff31e

import Definitions.Def_mm_classical
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Algebra.BigOperators.Fin

open scoped BigOperators
open MarkovMixing

/-- One step of the walk driven by the sign sequence `ω`. -/
private def stepOf {r : ℕ} (ω : Fin r → Bool) (i : Fin r) : ℤ := if ω i then 1 else -1

private lemma srw_succ {r : ℕ} (k : ℤ) (ω : Fin r → Bool) (t : ℕ) :
    srwPos k ω (t + 1)
      = srwPos k ω t + (if h : t < r then stepOf ω ⟨t, h⟩ else 0) := by
  classical
  unfold srwPos
  have hsplit : ∀ i : Fin r,
      (if (i : ℕ) < t + 1 then (if ω i then (1 : ℤ) else -1) else 0)
        = (if (i : ℕ) < t then (if ω i then (1 : ℤ) else -1) else 0)
          + (if (i : ℕ) = t then (if ω i then (1 : ℤ) else -1) else 0) := by
    intro i
    by_cases h1 : (i : ℕ) < t
    · have e1 : (i : ℕ) < t + 1 := by omega
      have e2 : ¬((i : ℕ) = t) := by omega
      rw [if_pos e1, if_pos h1, if_neg e2]; ring
    · by_cases h2 : (i : ℕ) = t
      · have e1 : (i : ℕ) < t + 1 := by omega
        rw [if_pos e1, if_neg h1, if_pos h2]; ring
      · have e1 : ¬((i : ℕ) < t + 1) := by omega
        rw [if_neg e1, if_neg h1, if_neg h2]; ring
  rw [Finset.sum_congr rfl fun i _ => hsplit i, Finset.sum_add_distrib]
  have hlast : (∑ i : Fin r, if (i : ℕ) = t then (if ω i then (1 : ℤ) else -1) else 0)
      = (if h : t < r then stepOf ω ⟨t, h⟩ else 0) := by
    by_cases h : t < r
    · rw [dif_pos h, Finset.sum_eq_single (⟨t, h⟩ : Fin r)]
      · rw [if_pos rfl]; rfl
      · intro i _ hi
        rw [if_neg]
        intro hc
        exact hi (Fin.ext hc)
      · intro hc; exact absurd (Finset.mem_univ _) hc
    · rw [dif_neg h]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [if_neg]
      have := i.isLt
      omega
  rw [hlast]
  ring

/-- Flipping every step from time `s` on. -/
private def flipAt {r : ℕ} (s : ℕ) (ω : Fin r → Bool) : Fin r → Bool :=
  fun i => if (i : ℕ) < s then ω i else !(ω i)

private lemma flipAt_flipAt {r : ℕ} (s : ℕ) (ω : Fin r → Bool) :
    flipAt s (flipAt s ω) = ω := by
  funext i
  unfold flipAt
  by_cases h : (i : ℕ) < s <;> simp [h]

private lemma stepOf_flipAt {r : ℕ} (s : ℕ) (ω : Fin r → Bool) (i : Fin r) :
    stepOf (flipAt s ω) i = if (i : ℕ) < s then stepOf ω i else -stepOf ω i := by
  unfold stepOf flipAt
  by_cases h : (i : ℕ) < s
  · simp [h]
  · by_cases hw : ω i <;> simp [h, hw]

/-- The reflected walk agrees with the original up to time `s` and is its reflection
in the level `srwPos k ω s` afterwards. -/
private lemma srw_flipAt {r : ℕ} (k : ℤ) (ω : Fin r → Bool) (s : ℕ) :
    ∀ t : ℕ, srwPos k (flipAt s ω) t
      = if t ≤ s then srwPos k ω t else 2 * srwPos k ω s - srwPos k ω t := by
  intro t
  induction t with
  | zero =>
      rw [if_pos (Nat.zero_le s)]
      simp [srwPos]
  | succ n ih =>
      rw [srw_succ, srw_succ, ih]
      by_cases h1 : n + 1 ≤ s
      · have hn : n ≤ s := by omega
        rw [if_pos h1, if_pos hn]
        by_cases hr : n < r
        · rw [dif_pos hr, dif_pos hr, stepOf_flipAt]
          rw [if_pos (by simpa using (by omega : n < s))]
        · rw [dif_neg hr, dif_neg hr]
      · rw [if_neg h1]
        by_cases hn : n ≤ s
        · -- then `n = s`
          have hns : n = s := by omega
          rw [if_pos hn]
          subst hns
          by_cases hr : n < r
          · rw [dif_pos hr, dif_pos hr, stepOf_flipAt, if_neg (by simp)]
            ring
          · rw [dif_neg hr, dif_neg hr]
            ring
        · rw [if_neg hn]
          by_cases hr : n < r
          · rw [dif_pos hr, dif_pos hr, stepOf_flipAt, if_neg (by simpa using (by omega : ¬ n < s))]
            ring
          · rw [dif_neg hr, dif_neg hr]
            ring

/-- The walk started at `k` visits `0` strictly before time `r`. -/
private def hitsZero {r : ℕ} (k : ℤ) (ω : Fin r → Bool) : Prop :=
  ∃ s : ℕ, s < r ∧ srwPos k ω s = 0

/-- The first time `< r` at which the walk is at `0` (junk value `0` otherwise). -/
private noncomputable def firstZero {r : ℕ} (k : ℤ) (ω : Fin r → Bool) : ℕ :=
  sInf {s : ℕ | s < r ∧ srwPos k ω s = 0}

private lemma firstZero_spec {r : ℕ} (k : ℤ) (ω : Fin r → Bool) (h : hitsZero k ω) :
    firstZero k ω < r ∧ srwPos k ω (firstZero k ω) = 0 := by
  obtain ⟨s, hs1, hs2⟩ := h
  exact Nat.sInf_mem (⟨s, hs1, hs2⟩ : {s : ℕ | s < r ∧ srwPos k ω s = 0}.Nonempty)

private lemma firstZero_min {r : ℕ} (k : ℤ) (ω : Fin r → Bool) (h : hitsZero k ω)
    (m : ℕ) (hm : m < firstZero k ω) : srwPos k ω m ≠ 0 := by
  intro hz
  have hlt : m < r := by
    have := (firstZero_spec k ω h).1
    omega
  have hmem : m ∈ {s : ℕ | s < r ∧ srwPos k ω s = 0} := ⟨hlt, hz⟩
  have hle : firstZero k ω ≤ m := Nat.sInf_le hmem
  omega

private lemma firstZero_le {r : ℕ} (k : ℤ) (ω : Fin r → Bool) (s : ℕ)
    (hs : s < r ∧ srwPos k ω s = 0) : firstZero k ω ≤ s :=
  Nat.sInf_le hs

/-- The trajectory reflected at its first visit to `0`. -/
private noncomputable def reflectPath {r : ℕ} (k : ℤ) (ω : Fin r → Bool) : Fin r → Bool :=
  flipAt (firstZero k ω) ω

private lemma reflect_below {r : ℕ} (k : ℤ) (ω : Fin r → Bool) (t : ℕ)
    (ht : t ≤ firstZero k ω) : srwPos k (reflectPath k ω) t = srwPos k ω t := by
  unfold reflectPath
  rw [srw_flipAt, if_pos ht]

private lemma reflect_firstZero {r : ℕ} (k : ℤ) (ω : Fin r → Bool) (h : hitsZero k ω) :
    hitsZero k (reflectPath k ω) ∧ firstZero k (reflectPath k ω) = firstZero k ω := by
  obtain ⟨hlt, hz⟩ := firstZero_spec k ω h
  have hz' : srwPos k (reflectPath k ω) (firstZero k ω) = 0 := by
    rw [reflect_below k ω _ (le_refl _)]; exact hz
  have h' : hitsZero k (reflectPath k ω) := ⟨firstZero k ω, hlt, hz'⟩
  refine ⟨h', le_antisymm (firstZero_le k _ _ ⟨hlt, hz'⟩) ?_⟩
  by_contra hc
  push Not at hc
  have hspec := firstZero_spec k (reflectPath k ω) h'
  refine firstZero_min k ω h (firstZero k (reflectPath k ω)) hc ?_
  rw [← reflect_below k ω (firstZero k (reflectPath k ω)) (le_of_lt hc)]
  exact hspec.2

private lemma reflect_end {r : ℕ} (k : ℤ) (ω : Fin r → Bool) (h : hitsZero k ω) :
    srwPos k (reflectPath k ω) r = - srwPos k ω r := by
  obtain ⟨hlt, hz⟩ := firstZero_spec k ω h
  unfold reflectPath
  rw [srw_flipAt, if_neg (by omega), hz]
  ring

private lemma reflect_reflect {r : ℕ} (k : ℤ) (ω : Fin r → Bool) (h : hitsZero k ω) :
    reflectPath k (reflectPath k ω) = ω := by
  show flipAt (firstZero k (reflectPath k ω)) (reflectPath k ω) = ω
  rw [(reflect_firstZero k ω h).2]
  exact flipAt_flipAt _ ω

/-- Discrete intermediate value theorem: a walk from `k > 0` ending below `0`
must have visited `0` strictly before the end. -/
private lemma hitsZero_of_neg {r : ℕ} (k : ℤ) (hk : 0 < k) (ω : Fin r → Bool)
    (hend : srwPos k ω r < 0) : hitsZero k ω := by
  have h0 : srwPos k ω 0 = k := by simp [srwPos]
  have hne : {t : ℕ | t ≤ r ∧ srwPos k ω t ≤ 0}.Nonempty := ⟨r, le_refl r, le_of_lt hend⟩
  obtain ⟨hler, hle0⟩ := Nat.sInf_mem hne
  set t₀ := sInf {t : ℕ | t ≤ r ∧ srwPos k ω t ≤ 0} with ht₀
  have hnz : t₀ ≠ 0 := by
    intro hc
    rw [hc, h0] at hle0
    omega
  obtain ⟨t₁, ht₁eq0⟩ := Nat.exists_eq_succ_of_ne_zero hnz
  have ht₁eq : t₀ = t₁ + 1 := ht₁eq0
  have hpos : 0 < srwPos k ω t₁ := by
    have hmin : t₁ ∉ {t : ℕ | t ≤ r ∧ srwPos k ω t ≤ 0} := fun hmem =>
      absurd (Nat.sInf_le hmem) (by omega)
    simp only [Set.mem_setOf_eq, not_and, not_le] at hmin
    exact hmin (by omega)
  have hr1 : t₁ < r := by omega
  have hstep := srw_succ k ω t₁
  rw [dif_pos hr1] at hstep
  have hs : stepOf ω ⟨t₁, hr1⟩ = 1 ∨ stepOf ω ⟨t₁, hr1⟩ = -1 := by
    unfold stepOf
    by_cases hw : ω ⟨t₁, hr1⟩ <;> simp [hw]
  have hle1 : srwPos k ω (t₁ + 1) ≤ 0 := by rw [← ht₁eq]; exact hle0
  have hzero : srwPos k ω (t₁ + 1) = 0 := by
    rcases hs with hs | hs <;> rw [hs] at hstep <;> omega
  refine ⟨t₁ + 1, ?_, hzero⟩
  have hlt : t₁ + 1 ≤ r := by rw [← ht₁eq]; exact hler
  rcases lt_or_eq_of_le hlt with h | h
  · exact h
  · rw [h] at hzero
    omega

theorem solution (r : ℕ) (k j : ℤ) (hk : 0 < k) (hj : 0 < j) :
    ((Finset.univ.filter fun ω : Fin r → Bool =>
        (∃ s < r, srwPos k ω s = 0) ∧ srwPos k ω r = j).card =
      (Finset.univ.filter fun ω : Fin r → Bool => srwPos k ω r = -j).card) ∧
    ((Finset.univ.filter fun ω : Fin r → Bool =>
        (∃ s < r, srwPos k ω s = 0) ∧ 0 < srwPos k ω r).card =
      (Finset.univ.filter fun ω : Fin r → Bool => srwPos k ω r < 0).card) := by
  classical
  constructor
  · refine Finset.card_nbij' (reflectPath k) (reflectPath k) ?_ ?_ ?_ ?_
    · intro ω hω
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hω ⊢
      rw [reflect_end k ω hω.1, hω.2]
    · intro ω hω
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hω ⊢
      have hz : hitsZero k ω := hitsZero_of_neg k hk ω (by rw [hω]; omega)
      refine ⟨(reflect_firstZero k ω hz).1, ?_⟩
      rw [reflect_end k ω hz, hω]
      ring
    · intro ω hω
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hω
      exact reflect_reflect k ω hω.1
    · intro ω hω
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hω
      exact reflect_reflect k ω (hitsZero_of_neg k hk ω (by rw [hω]; omega))
  · refine Finset.card_nbij' (reflectPath k) (reflectPath k) ?_ ?_ ?_ ?_
    · intro ω hω
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hω ⊢
      rw [reflect_end k ω hω.1]
      omega
    · intro ω hω
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hω ⊢
      have hz : hitsZero k ω := hitsZero_of_neg k hk ω hω
      refine ⟨(reflect_firstZero k ω hz).1, ?_⟩
      rw [reflect_end k ω hz]
      omega
    · intro ω hω
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hω
      exact reflect_reflect k ω hω.1
    · intro ω hω
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hω
      exact reflect_reflect k ω (hitsZero_of_neg k hk ω hω)
