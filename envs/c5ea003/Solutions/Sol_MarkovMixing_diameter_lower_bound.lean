-- Prove2me | solution 1 for MarkovMixing.diameter_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-08-22T04:18:09.703601+00:00
-- url     : https://prove2.me/submissions/735c299d-0a6e-462e-8d59-3c5261fefb1a

import Theorems.Thm_MarkovMixing_convergence_theorem
import Theorems.Thm_MarkovMixing_dist_le_distPairs
import Definitions.Def_mm_lower
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

open scoped BigOperators
open MarkovMixing

theorem solution {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (P : Matrix V V ℝ) (hP : IsStochastic P) (hirr : MarkovMixing.Irreducible P)
    (hap : Aperiodic P) (π : V → ℝ) (hπ : IsStationary P π)
    (ε : ℝ) (hε : 0 < ε) (hε2 : ε < 1 / 2) (x₀ y₀ : V) :
    (transGraph P).dist x₀ y₀ ≤ 2 * mixingTime P π ε := by
  classical
  set G := transGraph P with hG
  set T := mixingTime P π ε with hT
  have hpow_nonneg : ∀ (n : ℕ) (a b : V), 0 ≤ (P ^ n) a b := by
    intro n
    induction n with
    | zero => intro a b; by_cases hab : a = b <;> simp [Matrix.one_apply, hab]
    | succ m ih =>
        intro a b
        rw [pow_succ]
        exact Finset.sum_nonneg fun w _ => mul_nonneg (ih a w) (hP.1 w b)
  have hpow_row : ∀ (n : ℕ) (a : V), ∑ b, (P ^ n) a b = 1 := by
    intro n
    induction n with
    | zero => intro a; simp [Matrix.one_apply]
    | succ m ih =>
        intro a
        rw [pow_succ]
        have e : ∀ b : V, (P ^ m * P) a b = ∑ w, (P ^ m) a w * P w b := fun b => rfl
        rw [Finset.sum_congr rfl fun b _ => e b, Finset.sum_comm]
        rw [Finset.sum_congr rfl fun w _ => by rw [← Finset.mul_sum, hP.2 w, mul_one]]
        exact ih a
  -- a positive `n`-step transition gives a walk of length at most `n`
  have hwalk : ∀ (n : ℕ) (x z : V), 0 < (P ^ n) x z → ∃ p : G.Walk x z, p.length ≤ n := by
    intro n
    induction n with
    | zero =>
        intro x z hxz
        rw [pow_zero, Matrix.one_apply] at hxz
        by_cases h : x = z
        · subst h; exact ⟨SimpleGraph.Walk.nil, le_refl _⟩
        · rw [if_neg h] at hxz; linarith
    | succ m ih =>
        intro x z hxz
        rw [pow_succ] at hxz
        have hsum : (0:ℝ) < ∑ w, (P ^ m) x w * P w z := hxz
        obtain ⟨w, -, hw⟩ : ∃ w ∈ (Finset.univ : Finset V), 0 < (P ^ m) x w * P w z := by
          by_contra hcon
          push_neg at hcon
          have := Finset.sum_nonpos fun w hw => hcon w hw
          linarith
        have hw1 : 0 < (P ^ m) x w := by
          rcases lt_or_eq_of_le (hpow_nonneg m x w) with h | h
          · exact h
          · rw [← h, zero_mul] at hw; linarith
        have hw2 : 0 < P w z := by
          rcases lt_or_eq_of_le (hP.1 w z) with h | h
          · exact h
          · rw [← h, mul_zero] at hw; linarith
        obtain ⟨p, hp⟩ := ih x w hw1
        by_cases hwz : w = z
        · subst hwz
          exact ⟨p, by omega⟩
        · have hadj : G.Adj w z := by
            rw [hG, transGraph, SimpleGraph.fromRel_adj]
            exact ⟨hwz, Or.inl hw2⟩
          refine ⟨p.append (SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil), ?_⟩
          rw [SimpleGraph.Walk.length_append]
          simp only [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil]
          omega
  -- the mixing time is attained
  obtain ⟨α, hα, C, hC, hgeo⟩ := MarkovMixing.convergence_theorem P hP hirr hap π hπ
  have hattain : distStationary P π T ≤ ε := by
    have hne : {t : ℕ | distStationary P π t ≤ ε}.Nonempty := by
      obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (x := ε / C) (y := α) (by positivity) hα.2
      refine ⟨n, ?_⟩
      have h1 : C * α ^ n < C * (ε / C) := mul_lt_mul_of_pos_left hn hC
      have h2 : C * (ε / C) = ε := by field_simp
      have := hgeo n
      simp only [Set.mem_setOf_eq]
      linarith
    exact Nat.sInf_mem hne
  by_contra hcon
  push_neg at hcon
  -- the two `T`-step distributions have disjoint supports
  set S : Finset V := Finset.univ.filter (fun z => ∃ p : G.Walk x₀ z, p.length ≤ T) with hS
  have hin : ∀ z : V, 0 < (P ^ T) x₀ z → z ∈ S := by
    intro z hz
    rw [hS, Finset.mem_filter]
    exact ⟨Finset.mem_univ z, hwalk T x₀ z hz⟩
  have hout : ∀ z : V, 0 < (P ^ T) y₀ z → z ∉ S := by
    intro z hz hmem
    rw [hS, Finset.mem_filter] at hmem
    obtain ⟨p, hp⟩ := hmem.2
    obtain ⟨q, hq⟩ := hwalk T y₀ z hz
    have hjoin : G.dist x₀ y₀ ≤ (p.append q.reverse).length :=
      SimpleGraph.dist_le _
    rw [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse] at hjoin
    omega
  have hmass1 : ∑ z ∈ S, (rowDist P T x₀) z = 1 := by
    have hcompl : ∑ z ∈ Sᶜ, (P ^ T) x₀ z = 0 := by
      refine Finset.sum_eq_zero fun z hz => ?_
      rcases lt_or_eq_of_le (hpow_nonneg T x₀ z) with h | h
      · exact absurd (hin z h) (Finset.mem_compl.mp hz)
      · exact h.symm
    have hsplit : ∑ z ∈ Sᶜ, (P ^ T) x₀ z + ∑ z ∈ S, (P ^ T) x₀ z = 1 := by
      rw [Finset.sum_compl_add_sum]; exact hpow_row T x₀
    show ∑ z ∈ S, (P ^ T) x₀ z = 1
    linarith
  have hmass2 : ∑ z ∈ S, (rowDist P T y₀) z = 0 := by
    refine Finset.sum_eq_zero fun z hz => ?_
    rcases lt_or_eq_of_le (hpow_nonneg T y₀ z) with h | h
    · exact absurd hz (hout z h)
    · exact h.symm
  -- hence the two rows are at total variation distance one
  have hbdd : ∀ μ ν : V → ℝ,
      BddAbove (Set.range fun A : Finset V => |∑ x ∈ A, μ x - ∑ x ∈ A, ν x|) :=
    fun μ ν => Set.Finite.bddAbove
      (Set.range fun A : Finset V => |∑ x ∈ A, μ x - ∑ x ∈ A, ν x|).toFinite
  have hone : (1:ℝ) ≤ tvDist (rowDist P T x₀) (rowDist P T y₀) := by
    have h := le_ciSup (hbdd (rowDist P T x₀) (rowDist P T y₀)) S
    rw [hmass1, hmass2] at h
    simpa using h
  have hbdd_dbar : BddAbove
      (Set.range fun p : V × V => tvDist (rowDist P T p.1) (rowDist P T p.2)) :=
    Set.Finite.bddAbove
      (Set.range fun p : V × V => tvDist (rowDist P T p.1) (rowDist P T p.2)).toFinite
  have hdbar : (1:ℝ) ≤ distPairs P T :=
    le_trans hone (le_ciSup hbdd_dbar (x₀, y₀))
  have hfinal := (MarkovMixing.dist_le_distPairs P hP π hπ T).2
  linarith
