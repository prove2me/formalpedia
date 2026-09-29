-- Prove2me | solution 1 for MarkovMixing.counting_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-08-22T04:20:30.757572+00:00
-- url     : https://prove2.me/submissions/565de4df-2179-45dd-b221-2ad1f965b56c

import Theorems.Thm_MarkovMixing_convergence_theorem
import Definitions.Def_mm_lower
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

open scoped BigOperators
open MarkovMixing

theorem solution {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (P : Matrix V V ℝ) (hP : IsStochastic P) (hirr : MarkovMixing.Irreducible P)
    (hap : Aperiodic P) (hπ : IsStationary P (uniformDist V))
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    Real.log ((Fintype.card V : ℝ) * (1 - ε)) / Real.log (maxOutDegree P) ≤
      (mixingTime P (uniformDist V) ε : ℝ) := by
  classical
  set Δ : ℕ := maxOutDegree P with hΔ
  set T : ℕ := mixingTime P (uniformDist V) ε with hT
  have hcardpos : (0:ℝ) < (Fintype.card V : ℝ) := by exact_mod_cast Fintype.card_pos
  have hpow_nonneg : ∀ (n : ℕ) (a b : V), 0 ≤ (P ^ n) a b := by
    intro n
    induction n with
    | zero => intro a b; by_cases hab : a = b <;> simp [Matrix.one_apply, hab]
    | succ m ih =>
        intro a b
        rw [pow_succ]
        exact Finset.sum_nonneg fun w _ => mul_nonneg (ih a w) (hP.1 w b)
  -- the support of an `n`-step row has at most `Δ ^ n` states
  have hdeg : ∀ x : V, (Finset.univ.filter (fun y : V => 0 < P x y)).card ≤ Δ :=
    fun x => Finset.le_sup (f := fun x : V => (Finset.univ.filter fun y : V => 0 < P x y).card)
      (Finset.mem_univ x)
  have hsupp : ∀ (n : ℕ) (x : V),
      (Finset.univ.filter (fun z : V => 0 < (P ^ n) x z)).card ≤ Δ ^ n := by
    intro n
    induction n with
    | zero =>
        intro x
        have hsub : Finset.univ.filter (fun z : V => 0 < (P ^ 0) x z) ⊆ {x} := by
          intro z hz
          rw [Finset.mem_filter] at hz
          have := hz.2
          rw [pow_zero, Matrix.one_apply] at this
          by_cases h : x = z
          · simp [h]
          · rw [if_neg h] at this; linarith
        calc (Finset.univ.filter (fun z : V => 0 < (P ^ 0) x z)).card
            ≤ ({x} : Finset V).card := Finset.card_le_card hsub
          _ = 1 := Finset.card_singleton x
          _ = Δ ^ 0 := (pow_zero Δ).symm
    | succ m ih =>
        intro x
        set A : Finset V := Finset.univ.filter (fun w : V => 0 < (P ^ m) x w) with hA
        have hsub : Finset.univ.filter (fun z : V => 0 < (P ^ (m + 1)) x z)
            ⊆ A.biUnion (fun w => Finset.univ.filter (fun z : V => 0 < P w z)) := by
          intro z hz
          rw [Finset.mem_filter] at hz
          have hzz : (0:ℝ) < ∑ w, (P ^ m) x w * P w z := by
            have := hz.2
            rwa [pow_succ] at this
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
          refine Finset.mem_biUnion.mpr ⟨w, ?_, ?_⟩
          · rw [hA, Finset.mem_filter]; exact ⟨Finset.mem_univ w, hw1⟩
          · rw [Finset.mem_filter]; exact ⟨Finset.mem_univ z, hw2⟩
        calc (Finset.univ.filter (fun z : V => 0 < (P ^ (m + 1)) x z)).card
            ≤ (A.biUnion (fun w => Finset.univ.filter (fun z : V => 0 < P w z))).card :=
              Finset.card_le_card hsub
          _ ≤ ∑ w ∈ A, (Finset.univ.filter (fun z : V => 0 < P w z)).card :=
              Finset.card_biUnion_le
          _ ≤ ∑ _w ∈ A, Δ := Finset.sum_le_sum fun w _ => hdeg w
          _ = A.card * Δ := by rw [Finset.sum_const, smul_eq_mul]
          _ ≤ Δ ^ m * Δ := Nat.mul_le_mul_right Δ (ih x)
          _ = Δ ^ (m + 1) := (pow_succ Δ m).symm
  -- the mixing time is attained
  obtain ⟨α, hα, C, hC, hgeo⟩ := MarkovMixing.convergence_theorem P hP hirr hap _ hπ
  have hattain : distStationary P (uniformDist V) T ≤ ε := by
    have hne : {t : ℕ | distStationary P (uniformDist V) t ≤ ε}.Nonempty := by
      obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (x := ε / C) (y := α) (by positivity) hα.2
      refine ⟨n, ?_⟩
      have h1 : C * α ^ n < C * (ε / C) := mul_lt_mul_of_pos_left hn hC
      have h2 : C * (ε / C) = ε := by field_simp
      have := hgeo n
      simp only [Set.mem_setOf_eq]
      linarith
    exact Nat.sInf_mem hne
  -- the support bound forces a large distance to uniformity
  set x₀ : V := Classical.arbitrary V with hx₀
  set A : Finset V := Finset.univ.filter (fun z : V => 0 < (P ^ T) x₀ z) with hA
  have hbdd : ∀ μ ν : V → ℝ,
      BddAbove (Set.range fun B : Finset V => |∑ x ∈ B, μ x - ∑ x ∈ B, ν x|) :=
    fun μ ν => Set.Finite.bddAbove
      (Set.range fun B : Finset V => |∑ x ∈ B, μ x - ∑ x ∈ B, ν x|).toFinite
  have hzero : ∑ z ∈ Aᶜ, (rowDist P T x₀) z = 0 := by
    refine Finset.sum_eq_zero fun z hz => ?_
    rcases lt_or_eq_of_le (hpow_nonneg T x₀ z) with h | h
    · exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ z, h⟩) (Finset.mem_compl.mp hz)
    · exact h.symm
  have hunif : ∑ z ∈ Aᶜ, uniformDist V z = ((Aᶜ : Finset V).card : ℝ) * (Fintype.card V : ℝ)⁻¹ := by
    show ∑ _z ∈ Aᶜ, (Fintype.card V : ℝ)⁻¹ = _
    rw [Finset.sum_const, nsmul_eq_mul]
  have htv : ((Aᶜ : Finset V).card : ℝ) * (Fintype.card V : ℝ)⁻¹
      ≤ distStationary P (uniformDist V) T := by
    have h1 := le_ciSup (hbdd (rowDist P T x₀) (uniformDist V)) Aᶜ
    rw [hzero, hunif] at h1
    have h2 : |(0:ℝ) - ((Aᶜ : Finset V).card : ℝ) * (Fintype.card V : ℝ)⁻¹|
        = ((Aᶜ : Finset V).card : ℝ) * (Fintype.card V : ℝ)⁻¹ := by
      rw [zero_sub, abs_neg, abs_of_nonneg (by positivity)]
    rw [h2] at h1
    have hbdd_d : BddAbove (Set.range fun x : V => tvDist (rowDist P T x) (uniformDist V)) :=
      Set.Finite.bddAbove
        (Set.range fun x : V => tvDist (rowDist P T x) (uniformDist V)).toFinite
    exact le_trans h1 (le_ciSup hbdd_d x₀)
  -- turn the count into the inequality `|V| (1 - ε) ≤ Δ ^ T`
  have hcards : ((Aᶜ : Finset V).card : ℝ) + (A.card : ℝ) = (Fintype.card V : ℝ) := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) (Finset.card_compl_add_card A)
  have hAle : (A.card : ℝ) ≤ ((Δ ^ T : ℕ) : ℝ) := by exact_mod_cast hsupp T x₀
  have hkey : (Fintype.card V : ℝ) * (1 - ε) ≤ ((Δ ^ T : ℕ) : ℝ) := by
    have h1 : ((Aᶜ : Finset V).card : ℝ) * (Fintype.card V : ℝ)⁻¹ ≤ ε := le_trans htv hattain
    have h2 : ((Aᶜ : Finset V).card : ℝ) ≤ ε * (Fintype.card V : ℝ) := by
      have h3 := mul_le_mul_of_nonneg_right h1 hcardpos.le
      rw [mul_assoc, inv_mul_cancel₀ hcardpos.ne', mul_one] at h3
      exact h3
    nlinarith [hcards, hAle, h2]
  -- conclude, taking logarithms
  have hΔ1 : 1 ≤ Δ := by
    obtain ⟨y, -, hy⟩ : ∃ y ∈ (Finset.univ : Finset V), 0 < P x₀ y := by
      by_contra hcon
      push_neg at hcon
      have h := Finset.sum_nonpos fun y hy => hcon y hy
      rw [hP.2 x₀] at h
      linarith
    have hne : (Finset.univ.filter (fun y : V => 0 < P x₀ y)).Nonempty :=
      ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ y, hy⟩⟩
    exact le_trans (Finset.card_pos.mpr hne) (hdeg x₀)
  have hΔR : (1:ℝ) ≤ (Δ : ℝ) := by exact_mod_cast hΔ1
  rcases eq_or_lt_of_le hΔR with hone | hgt
  · -- `Δ = 1`: the logarithm in the denominator vanishes and the bound is trivial
    have : Real.log (Δ : ℝ) = 0 := by rw [← hone, Real.log_one]
    rw [this, div_zero]
    positivity
  · have hlogpos : 0 < Real.log (Δ : ℝ) := Real.log_pos hgt
    rw [div_le_iff₀ hlogpos]
    have hposarg : (0:ℝ) < (Fintype.card V : ℝ) * (1 - ε) := by
      have : (0:ℝ) < 1 - ε := by linarith
      positivity
    calc Real.log ((Fintype.card V : ℝ) * (1 - ε))
        ≤ Real.log (((Δ ^ T : ℕ) : ℝ)) := Real.log_le_log hposarg hkey
      _ = Real.log ((Δ : ℝ) ^ T) := by push_cast; ring_nf
      _ = (T : ℝ) * Real.log (Δ : ℝ) := by rw [Real.log_pow]
