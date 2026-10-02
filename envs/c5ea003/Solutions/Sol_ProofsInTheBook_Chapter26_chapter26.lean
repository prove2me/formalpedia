-- Prove2me | solution 1 for ProofsInTheBook.Chapter26.chapter26
-- status  : ACCEPTED   (prove)
-- author  : @xiangyazi24
-- created : 2026-09-12T16:13:04.006221+00:00
-- url     : https://prove2.me/submissions/87391b40-cbc8-4559-9bda-61d26880bb52

import Mathlib
import Definitions.Def_ProofsInTheBook_Chapter26


/-!
# Chapter 26: Pigeon-hole and double counting

From "Proofs from THE BOOK":

**Erdős-Szekeres theorem**: Every sequence of n²+1 pairwise distinct real numbers
contains either a strictly increasing subsequence of length ≥ n+1, or a strictly
decreasing subsequence of length ≥ n+1.

*Book proof (Seidenberg 1959).* Assign to each element aᵢ the pair
(length of longest increasing subsequence ending at aᵢ, length of longest
decreasing subsequence ending at aᵢ). These pairs are all distinct: if i < j
and aᵢ < aⱼ then the first component strictly increases; if aᵢ > aⱼ the second
strictly increases. If all labels lie in {1,..,n}², there are only n² distinct
labels — contradicting n²+1 elements by pigeonhole.
-/

namespace ProofsInTheBook.Chapter26

open Finset Function

/-! ### Length of longest monotone subsequence ending at a position -/

















private lemma one_le_lisAt {m : ℕ} (a : Fin m → ℝ) (i : Fin m) : 1 ≤ lisAt a i :=
  Finset.le_max' _ _ (Finset.mem_image.mpr
    ⟨{i}, singleton_mem_incFilter a i, Finset.card_singleton _⟩)

private lemma one_le_ldsAt {m : ℕ} (a : Fin m → ℝ) (i : Fin m) : 1 ≤ ldsAt a i :=
  Finset.le_max' _ _ (Finset.mem_image.mpr
    ⟨{i}, singleton_mem_decFilter a i, Finset.card_singleton _⟩)

/-! ### Key injectivity: the (lisAt, ldsAt) label distinguishes positions -/

/-- If i < j and a(i) < a(j), then the LIS ending at j is strictly longer. -/
private lemma lisAt_lt_of_lt {m : ℕ} {a : Fin m → ℝ} (_ha : Injective a)
    {i j : Fin m} (hij : i < j) (haij : a i < a j) :
    lisAt a i < lisAt a j := by
  -- Extract the optimal IS S of length lisAt a i ending at i
  have hmem : lisAt a i ∈ incLengths a i := Finset.max'_mem _ _
  simp only [incLengths, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
    true_and] at hmem
  obtain ⟨S, ⟨hiS, hbound, hmono⟩, hcard⟩ := hmem
  -- j ∉ S since every element of S satisfies k ≤ i < j
  have hjS : j ∉ S := fun h => absurd (hbound j h) (not_le.mpr hij)
  -- S ∪ {j} has cardinality lisAt a i + 1
  have hlen : (S ∪ {j}).card = lisAt a i + 1 := by
    have hdisj : Disjoint S ({j} : Finset _) := Finset.disjoint_singleton_right.mpr hjS
    rw [Finset.card_union_of_disjoint hdisj, Finset.card_singleton]
    omega
  -- S ∪ {j} is strictly increasing: for x ∈ S and y = j, a(x) ≤ a(i) < a(j)
  have hmono' : StrictMonoOn a (↑(S ∪ {j}) : Set (Fin m)) := by
    intro x hx y hy hxy
    simp only [Finset.coe_union, Finset.coe_singleton,
      Set.mem_union, Set.mem_singleton_iff] at hx hy
    rcases hx with hxS | rfl
    · rcases hy with hyS | rfl
      · exact hmono hxS hyS hxy
      · -- x ∈ S, y = j: a(x) ≤ a(i) < a(j)
        have hxi := hbound x hxS
        have hax_le : a x ≤ a i := by
          rcases eq_or_lt_of_le hxi with rfl | h
          · exact le_refl _
          · exact le_of_lt (hmono hxS (Finset.mem_coe.mpr hiS) h)
        linarith
    · rcases hy with hyS | rfl
      · -- x = j, y ∈ S: impossible since y ≤ i < j = x
        exact absurd hxy (not_lt.mpr ((hbound y hyS).trans hij.le))
      · exact absurd hxy (lt_irrefl _)
  -- So lisAt a j ≥ |S ∪ {j}| = lisAt a i + 1
  have hle : lisAt a i + 1 ≤ lisAt a j :=
    Finset.le_max' _ _ (by
      simp only [incLengths, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨S ∪ {j}, ⟨?_, ?_, hmono'⟩, hlen⟩
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_singleton_self j))
      · intro k hk
        simp only [Finset.mem_union, Finset.mem_singleton] at hk
        exact hk.elim (fun h => (hbound k h).trans hij.le) (fun h => h ▸ le_refl j))
  omega

/-- If i < j and a(i) > a(j), then the LDS ending at j is strictly longer. -/
private lemma ldsAt_lt_of_gt {m : ℕ} {a : Fin m → ℝ} (_ha : Injective a)
    {i j : Fin m} (hij : i < j) (haij : a j < a i) :
    ldsAt a i < ldsAt a j := by
  -- Extract the optimal DS S of length ldsAt a i ending at i
  have hmem : ldsAt a i ∈ decLengths a i := Finset.max'_mem _ _
  simp only [decLengths, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
    true_and] at hmem
  obtain ⟨S, ⟨hiS, hbound, hanti⟩, hcard⟩ := hmem
  have hjS : j ∉ S := fun h => absurd (hbound j h) (not_le.mpr hij)
  have hlen : (S ∪ {j}).card = ldsAt a i + 1 := by
    have hdisj : Disjoint S ({j} : Finset _) := Finset.disjoint_singleton_right.mpr hjS
    rw [Finset.card_union_of_disjoint hdisj, Finset.card_singleton]
    omega
  -- S ∪ {j} is strictly decreasing: for x ∈ S, a(j) < a(i) ≤ a(x)
  have hanti' : StrictAntiOn a (↑(S ∪ {j}) : Set (Fin m)) := by
    intro x hx y hy hxy
    simp only [Finset.coe_union, Finset.coe_singleton,
      Set.mem_union, Set.mem_singleton_iff] at hx hy
    rcases hx with hxS | rfl
    · rcases hy with hyS | rfl
      · exact hanti hxS hyS hxy
      · -- x ∈ S, y = j: need a(j) < a(x), i.e., a(y) < a(x)
        have hxi := hbound x hxS
        have hax_ge : a i ≤ a x := by
          rcases eq_or_lt_of_le hxi with rfl | h
          · exact le_refl _
          · exact le_of_lt (hanti hxS (Finset.mem_coe.mpr hiS) h)
        linarith
    · rcases hy with hyS | rfl
      · exact absurd hxy (not_lt.mpr ((hbound y hyS).trans hij.le))
      · exact absurd hxy (lt_irrefl _)
  have hle : ldsAt a i + 1 ≤ ldsAt a j :=
    Finset.le_max' _ _ (by
      simp only [decLengths, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨S ∪ {j}, ⟨?_, ?_, hanti'⟩, hlen⟩
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_singleton_self j))
      · intro k hk
        simp only [Finset.mem_union, Finset.mem_singleton] at hk
        exact hk.elim (fun h => (hbound k h).trans hij.le) (fun h => h ▸ le_refl j))
  omega

/-- The label map (lisAt, ldsAt) is injective. -/
private lemma label_injective {m : ℕ} {a : Fin m → ℝ} (ha : Injective a) :
    Injective (fun i => (lisAt a i, ldsAt a i)) := by
  intro i j hlabels
  rcases lt_trichotomy i j with h | rfl | h
  · -- i < j: a i ≠ a j, either increasing or decreasing
    rcases lt_or_gt_of_ne (ha.ne h.ne) with hlt | hgt
    · exact absurd (congr_arg Prod.fst hlabels) (lisAt_lt_of_lt ha h hlt).ne
    · exact absurd (congr_arg Prod.snd hlabels) (ldsAt_lt_of_gt ha h hgt).ne
  · rfl
  · -- h : j < i (Lean: i > j means j < i): a i ≠ a j
    rcases lt_or_gt_of_ne (ha.ne h.ne') with hlt | hgt
    · -- a i < a j, j < i positions: decreasing from j to i
      exact absurd (congr_arg Prod.snd hlabels) (ldsAt_lt_of_gt ha h hlt).ne'
    · -- a j < a i (a i > a j), j < i positions: increasing from j to i
      exact absurd (congr_arg Prod.fst hlabels) (lisAt_lt_of_lt ha h hgt).ne'

/-! ### Main theorem -/

/--
**Erdős-Szekeres theorem**: Any injective sequence of n²+1 real numbers
contains a monotone subsequence (increasing or decreasing) of length ≥ n+1.
-/
theorem chapter26_erdos_szekeres (n : ℕ)
    {a : Fin (n ^ 2 + 1) → ℝ} (ha : Injective a) :
    (∃ t : Finset (Fin (n ^ 2 + 1)), n + 1 ≤ t.card ∧ StrictMonoOn a ↑t) ∨
    (∃ t : Finset (Fin (n ^ 2 + 1)), n + 1 ≤ t.card ∧ StrictAntiOn a ↑t) := by
  by_contra h
  push Not at h
  obtain ⟨h_inc, h_dec⟩ := h
  -- All LIS ≤ n and LDS ≤ n for every position
  have hlis : ∀ i, lisAt a i ≤ n := by
    intro i
    by_contra hi
    simp only [not_le] at hi
    have hmem : lisAt a i ∈ incLengths a i := Finset.max'_mem _ _
    simp only [incLengths, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
      true_and] at hmem
    obtain ⟨S, ⟨_, hbound, hmono⟩, hcard⟩ := hmem
    exact absurd hmono (h_inc S (by omega))
  have hlds : ∀ i, ldsAt a i ≤ n := by
    intro i
    by_contra hi
    simp only [not_le] at hi
    have hmem : ldsAt a i ∈ decLengths a i := Finset.max'_mem _ _
    simp only [decLengths, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
      true_and] at hmem
    obtain ⟨S, ⟨_, hbound, hanti⟩, hcard⟩ := hmem
    exact absurd hanti (h_dec S (by omega))
  -- Pigeonhole: n²+1 positions map injectively into Fin n × Fin n of size n²
  have hinj := label_injective ha
  have hle : n ^ 2 + 1 ≤ n ^ 2 := by
    have : Fintype.card (Fin (n ^ 2 + 1)) ≤ Fintype.card (Fin n × Fin n) :=
      Fintype.card_le_of_injective
        (fun i => (⟨lisAt a i - 1, by have h1 := one_le_lisAt a i; have h2 := hlis i; omega⟩,
                   ⟨ldsAt a i - 1, by have h1 := one_le_ldsAt a i; have h2 := hlds i; omega⟩))
        (fun i j hij => by
          simp only [Prod.mk.injEq, Fin.mk.injEq] at hij
          obtain ⟨hfst, hsnd⟩ := hij
          have h1 := one_le_lisAt a i; have h2 := one_le_lisAt a j
          have h3 := one_le_ldsAt a i; have h4 := one_le_ldsAt a j
          exact hinj (show (lisAt a i, ldsAt a i) = (lisAt a j, ldsAt a j) from
            Prod.ext (by omega) (by omega)))
    simp only [Fintype.card_fin, Fintype.card_prod, pow_two] at this
    omega
  omega



end ProofsInTheBook.Chapter26

open Finset Function
open ProofsInTheBook.Chapter26

theorem solution (n : ℕ) {a : Fin (n ^ 2 + 1) → ℝ} (ha : Injective a) :
    (∃ t : Finset (Fin (n ^ 2 + 1)), n + 1 ≤ t.card ∧ StrictMonoOn a ↑t) ∨
    (∃ t : Finset (Fin (n ^ 2 + 1)), n + 1 ≤ t.card ∧ StrictAntiOn a ↑t) :=
  chapter26_erdos_szekeres n ha
