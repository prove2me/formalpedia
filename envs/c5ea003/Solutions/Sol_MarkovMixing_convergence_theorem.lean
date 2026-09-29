-- Prove2me | solution 1 for MarkovMixing.convergence_theorem
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-08-22T04:09:04.159386+00:00
-- url     : https://prove2.me/submissions/7d10cd95-f53a-48d3-bf99-1f77559dfc0b

import Theorems.Thm_MarkovMixing_exists_pow_pos
import Theorems.Thm_MarkovMixing_dist_le_distPairs
import Theorems.Thm_MarkovMixing_distPairs_submultiplicative
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

open scoped BigOperators
open MarkovMixing

theorem solution {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (P : Matrix V V ℝ) (hP : IsStochastic P) (hirr : MarkovMixing.Irreducible P)
    (hap : Aperiodic P) (π : V → ℝ) (hπ : IsStationary P π) :
    ∃ α : ℝ, α ∈ Set.Ioo (0 : ℝ) 1 ∧ ∃ C : ℝ, 0 < C ∧
      ∀ t : ℕ, distStationary P π t ≤ C * α ^ t := by
  classical
  -- rows of every power are probability distributions
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
  -- generic supremum facts
  have hbdd : ∀ μ ν : V → ℝ,
      BddAbove (Set.range fun A : Finset V => |∑ x ∈ A, μ x - ∑ x ∈ A, ν x|) :=
    fun μ ν => Set.Finite.bddAbove
      (Set.range fun A : Finset V => |∑ x ∈ A, μ x - ∑ x ∈ A, ν x|).toFinite
  have htv_ge : ∀ (μ ν : V → ℝ) (A : Finset V),
      |∑ x ∈ A, μ x - ∑ x ∈ A, ν x| ≤ tvDist μ ν :=
    fun μ ν A => le_ciSup (hbdd μ ν) A
  have htv_le : ∀ (μ ν : V → ℝ) (c : ℝ),
      (∀ A : Finset V, |∑ x ∈ A, μ x - ∑ x ∈ A, ν x| ≤ c) → tvDist μ ν ≤ c :=
    fun μ ν c h => ciSup_le h
  have htv_nonneg : ∀ μ ν : V → ℝ, 0 ≤ tvDist μ ν := by
    intro μ ν
    have h := htv_ge μ ν ∅
    simpa using h
  have hbdd_dbar : ∀ n : ℕ,
      BddAbove (Set.range fun p : V × V => tvDist (rowDist P n p.1) (rowDist P n p.2)) :=
    fun n => Set.Finite.bddAbove
      (Set.range fun p : V × V => tvDist (rowDist P n p.1) (rowDist P n p.2)).toFinite
  have hdbar_ge : ∀ (n : ℕ) (x y : V),
      tvDist (rowDist P n x) (rowDist P n y) ≤ distPairs P n :=
    fun n x y => le_ciSup (hbdd_dbar n) (x, y)
  have hdbar_le : ∀ (n : ℕ) (c : ℝ),
      (∀ x y : V, tvDist (rowDist P n x) (rowDist P n y) ≤ c) → distPairs P n ≤ c := by
    intro n c h
    exact ciSup_le fun p => h p.1 p.2
  have hdbar_nonneg : ∀ n : ℕ, 0 ≤ distPairs P n := fun n =>
    le_trans (htv_nonneg _ _) (hdbar_ge n (Classical.arbitrary V) (Classical.arbitrary V))
  -- every row distance is at most one
  have hdbar_le_one : ∀ n : ℕ, distPairs P n ≤ 1 := by
    intro n
    refine hdbar_le n 1 fun x y => htv_le _ _ _ fun A => ?_
    have h1 : (0:ℝ) ≤ ∑ z ∈ A, (rowDist P n x) z :=
      Finset.sum_nonneg fun z _ => hpow_nonneg n x z
    have h2 : (0:ℝ) ≤ ∑ z ∈ A, (rowDist P n y) z :=
      Finset.sum_nonneg fun z _ => hpow_nonneg n y z
    have h3 : ∑ z ∈ A, (rowDist P n x) z ≤ 1 := by
      rw [← hpow_row n x]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A)
        (fun z _ _ => hpow_nonneg n x z)
    have h4 : ∑ z ∈ A, (rowDist P n y) z ≤ 1 := by
      rw [← hpow_row n y]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A)
        (fun z _ _ => hpow_nonneg n y z)
    rw [abs_le]
    constructor <;> linarith
  -- `d̄` is nonincreasing, by submultiplicativity
  have hdbar_mono : ∀ n m : ℕ, distPairs P (n + m) ≤ distPairs P n := by
    intro n m
    calc distPairs P (n + m) ≤ distPairs P n * distPairs P m :=
          MarkovMixing.distPairs_submultiplicative P hP n m
      _ ≤ distPairs P n * 1 :=
          mul_le_mul_of_nonneg_left (hdbar_le_one m) (hdbar_nonneg n)
      _ = distPairs P n := mul_one _
  -- a uniformly positive power gives a strict contraction
  obtain ⟨r, hr0, hrpos⟩ := MarkovMixing.exists_pow_pos P hP hirr hap
  have hunivne : (Finset.univ : Finset (V × V)).Nonempty :=
    ⟨(Classical.arbitrary V, Classical.arbitrary V), Finset.mem_univ _⟩
  set θ : ℝ := Finset.univ.inf' hunivne (fun p : V × V => (P ^ r) p.1 p.2) with hθdef
  have hθle : ∀ x y : V, θ ≤ (P ^ r) x y := by
    intro x y
    exact Finset.inf'_le (fun p : V × V => (P ^ r) p.1 p.2) (Finset.mem_univ (x, y))
  have hθpos : 0 < θ := by
    rw [hθdef, Finset.lt_inf'_iff]
    exact fun p _ => hrpos p.1 p.2
  have hcardpos : (0:ℝ) < (Fintype.card V : ℝ) := by exact_mod_cast Fintype.card_pos
  have hmassge : ∀ (x : V) (A : Finset V), θ * (A.card : ℝ) ≤ ∑ z ∈ A, (rowDist P r x) z := by
    intro x A
    calc θ * (A.card : ℝ) = ∑ _z ∈ A, θ := by rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ ∑ z ∈ A, (rowDist P r x) z := Finset.sum_le_sum fun z _ => hθle x z
  have hmassle : ∀ (x : V) (A : Finset V),
      ∑ z ∈ A, (rowDist P r x) z ≤ 1 - θ * ((Aᶜ : Finset V).card : ℝ) := by
    intro x A
    have hsum : ∑ z ∈ Aᶜ, (rowDist P r x) z + ∑ z ∈ A, (rowDist P r x) z = 1 := by
      rw [Finset.sum_compl_add_sum]
      exact hpow_row r x
    have := hmassge x Aᶜ
    linarith
  have hcontract : distPairs P r ≤ 1 - θ * (Fintype.card V : ℝ) := by
    refine hdbar_le r _ fun x y => htv_le _ _ _ fun A => ?_
    have hcards : ((Aᶜ : Finset V).card : ℝ) + (A.card : ℝ) = (Fintype.card V : ℝ) := by
      exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) (Finset.card_compl_add_card A)
    have h1 := hmassle x A
    have h2 := hmassge y A
    have h3 := hmassle y A
    have h4 := hmassge x A
    rw [abs_le]
    constructor <;> nlinarith [hcards]
  have hlt1 : distPairs P r < 1 := by
    have : 0 < θ * (Fintype.card V : ℝ) := mul_pos hθpos hcardpos
    linarith [hcontract]
  -- a contraction factor bounded away from both 0 and 1
  set β : ℝ := max (distPairs P r) (1/2) with hβdef
  have hβ1 : β < 1 := max_lt hlt1 (by norm_num)
  have hβhalf : (1:ℝ)/2 ≤ β := le_max_right _ _
  have hβpos : 0 < β := by linarith
  have hdbar_r_le : distPairs P r ≤ β := le_max_left _ _
  have hpowk : ∀ k : ℕ, distPairs P (k * r) ≤ β ^ k := by
    intro k
    induction k with
    | zero => simpa using hdbar_le_one 0
    | succ m ih =>
        have hstep : distPairs P ((m + 1) * r) ≤ distPairs P (m * r) * distPairs P r := by
          have h := MarkovMixing.distPairs_submultiplicative P hP (m * r) r
          rwa [show m * r + r = (m + 1) * r by ring] at h
        calc distPairs P ((m + 1) * r) ≤ distPairs P (m * r) * distPairs P r := hstep
          _ ≤ β ^ m * β :=
              mul_le_mul ih hdbar_r_le (hdbar_nonneg r) (pow_nonneg hβpos.le m)
          _ = β ^ (m + 1) := (pow_succ β m).symm
  -- assemble the geometric bound
  refine ⟨β ^ ((r : ℝ)⁻¹), ⟨Real.rpow_pos_of_pos hβpos _, ?_⟩, β⁻¹, by positivity, ?_⟩
  · have hrpos' : (0:ℝ) < (r : ℝ) := by exact_mod_cast hr0
    calc β ^ ((r : ℝ)⁻¹) < 1 ^ ((r : ℝ)⁻¹) :=
          Real.rpow_lt_rpow hβpos.le hβ1 (by positivity)
      _ = 1 := Real.one_rpow _
  · intro t
    have hrpos' : (0:ℝ) < (r : ℝ) := by exact_mod_cast hr0
    set k : ℕ := t / r with hkdef
    have hkr : k * r ≤ t := Nat.div_mul_le_self t r
    have hd : distStationary P π t ≤ distPairs P t :=
      (MarkovMixing.dist_le_distPairs P hP π hπ t).1
    have hmono : distPairs P t ≤ distPairs P (k * r) := by
      have h := hdbar_mono (k * r) (t - k * r)
      rwa [show k * r + (t - k * r) = t by omega] at h
    have hbound : distStationary P π t ≤ β ^ k :=
      le_trans hd (le_trans hmono (hpowk k))
    -- compare `β ^ k` with `β⁻¹ * (β ^ (1/r)) ^ t`
    have hexp : ((β ^ ((r : ℝ)⁻¹)) ^ t) = β ^ ((t : ℝ) / (r : ℝ)) := by
      rw [← Real.rpow_natCast (β ^ ((r : ℝ)⁻¹)) t, ← Real.rpow_mul hβpos.le]
      congr 1
      field_simp
    have hlt : (t : ℝ) / (r : ℝ) ≤ (k : ℝ) + 1 := by
      rw [div_le_iff₀ hrpos']
      have h : t < (k + 1) * r := by
        have h1 : r * k + t % r = t := Nat.div_add_mod t r
        have h2 : t % r < r := Nat.mod_lt t hr0
        calc t = r * k + t % r := h1.symm
          _ < r * k + r := by omega
          _ = (k + 1) * r := by ring
      have : (t : ℝ) ≤ ((k + 1) * r : ℕ) := by exact_mod_cast h.le
      push_cast at this
      linarith
    have hstep : β ^ ((k : ℝ) + 1) ≤ β ^ ((t : ℝ) / (r : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_ge hβpos hβ1.le hlt
    have hrewrite : β ^ ((k : ℝ) + 1) = β ^ (k + 1) := by
      rw [show ((k : ℝ) + 1) = ((k + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    rw [hexp]
    rw [hrewrite] at hstep
    have hfinal : β ^ k ≤ β⁻¹ * β ^ ((t : ℝ) / (r : ℝ)) := by
      have h1 : β⁻¹ * β ^ (k + 1) = β ^ k := by
        rw [pow_succ]
        field_simp
      calc β ^ k = β⁻¹ * β ^ (k + 1) := h1.symm
        _ ≤ β⁻¹ * β ^ ((t : ℝ) / (r : ℝ)) :=
            mul_le_mul_of_nonneg_left hstep (by positivity)
    linarith [hbound, hfinal]
