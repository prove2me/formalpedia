-- Prove2me | solution 1 for zarankiewicz_ks_t_problem
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:11:05.747854+00:00
-- url     : https://prove2.me/submissions/32ffcc62-d583-4185-9c49-520a8d7e71dc

import Mathlib

-- Source module: Counting.lean
open Finset

section
variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

def commonNeighborFinset (A : Finset V) : Finset V :=
  univ.filter (fun v => A ⊆ G.neighborFinset v)

theorem commonNeighborFinset_card_lt (s t : ℕ)
    (hfree : ¬∃ A B : Finset V, A.card = s ∧ B.card = t ∧
      ∀ a ∈ A, ∀ b ∈ B, G.Adj a b)
    (A : Finset V) (hA : A.card = s) :
    (commonNeighborFinset G A).card < t := by
  classical
  by_contra h
  obtain ⟨B, hB, hcard⟩ := exists_subset_card_eq (Nat.le_of_not_gt h)
  apply hfree
  refine ⟨A, B, hA, hcard, ?_⟩
  intro a ha b hb
  have hsub : A ⊆ G.neighborFinset b := (mem_filter.mp (hB hb)).2
  exact ((G.mem_neighborFinset b a).mp (hsub ha)).symm

/-- Count incidences between a vertex and an `s`-subset of its neighborhood. -/
theorem sum_choose_degree_eq_sum_common (s : ℕ) :
    (∑ v : V, (G.degree v).choose s) =
      ∑ A ∈ (univ : Finset V).powersetCard s, (commonNeighborFinset G A).card := by
  classical
  let family := (univ : Finset V).powersetCard s
  let r : V → Finset V → Prop := fun v A => A ⊆ G.neighborFinset v
  have habove (v : V) : family.bipartiteAbove r v = (G.neighborFinset v).powersetCard s := by
    ext A
    simp only [family, bipartiteAbove, mem_filter, mem_powersetCard, subset_univ, true_and, r]
    exact and_comm
  have hbelow (A : Finset V) : (univ : Finset V).bipartiteBelow r A =
      commonNeighborFinset G A := rfl
  calc
    (∑ v : V, (G.degree v).choose s) = ∑ v : V, (family.bipartiteAbove r v).card := by
      apply sum_congr rfl
      intro v _
      rw [habove, card_powersetCard, G.card_neighborFinset_eq_degree]
    _ = ∑ A ∈ family, ((univ : Finset V).bipartiteBelow r A).card :=
      sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow r
    _ = ∑ A ∈ (univ : Finset V).powersetCard s, (commonNeighborFinset G A).card := by
      simp only [hbelow, family]

theorem sum_choose_degree_le (s t : ℕ) (ht : 1 ≤ t)
    (hfree : ¬∃ A B : Finset V, A.card = s ∧ B.card = t ∧
      ∀ a ∈ A, ∀ b ∈ B, G.Adj a b) :
    (∑ v : V, (G.degree v).choose s) ≤ (t - 1) * (Fintype.card V).choose s := by
  classical
  rw [sum_choose_degree_eq_sum_common]
  calc
    (∑ A ∈ (univ : Finset V).powersetCard s, (commonNeighborFinset G A).card) ≤
        ∑ _A ∈ (univ : Finset V).powersetCard s, (t - 1) := by
      apply sum_le_sum
      intro A hA
      apply Nat.le_of_lt_succ
      simpa only [Nat.succ_eq_add_one, Nat.sub_add_cancel ht] using
        commonNeighborFinset_card_lt G s t hfree A (mem_powersetCard.mp hA).2
    _ = (t - 1) * (Fintype.card V).choose s := by
      simp [mul_comm]

theorem sum_choose_degree_le_fin {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s t : ℕ) (ht : 1 ≤ t)
    (hfree : ¬∃ A B : Finset (Fin n), A.card = s ∧ B.card = t ∧
      ∀ a ∈ A, ∀ b ∈ B, G.Adj a b) :
    (∑ v : Fin n, (G.degree v).choose s) ≤ (t - 1) * n.choose s := by
  simpa only [Fintype.card_fin] using sum_choose_degree_le G s t ht hfree

end
-- Source module: Moments.lean
open Finset

section
theorem shifted_moment_bound (n s t : ℕ) (d : Fin n → ℕ)
    (hcount : ∑ v, (d v).choose s ≤ (t - 1) * n.choose s) :
    ∑ v, (d v + 1 - s) ^ s ≤ (t - 1) * n ^ s := by
  calc
    ∑ v, (d v + 1 - s) ^ s ≤ ∑ v, (d v).descFactorial s :=
      sum_le_sum (fun v _ => Nat.pow_sub_le_descFactorial (d v) s)
    _ = s.factorial * ∑ v, (d v).choose s := by
      simp_rw [Nat.descFactorial_eq_factorial_mul_choose]
      rw [mul_sum]
    _ ≤ s.factorial * ((t - 1) * n.choose s) := Nat.mul_le_mul_left _ hcount
    _ = (t - 1) * n.descFactorial s := by
      rw [Nat.descFactorial_eq_factorial_mul_choose]
      ring
    _ ≤ (t - 1) * n ^ s := Nat.mul_le_mul_left _ (Nat.descFactorial_le_pow n s)

theorem mean_pow_le (n s : ℕ) (hn : 0 < n) (x : Fin n → ℝ)
    (hx : ∀ v, 0 ≤ x v) :
    ((∑ v, x v) / n) ^ s ≤ (∑ v, x v ^ s) / n := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have h := Real.pow_arith_mean_le_arith_mean_pow univ (fun _ : Fin n => (n : ℝ)⁻¹)
    x (fun _ _ => by positivity) (by simp [hn0]) (fun v _ => hx v) s
  simp only [← mul_sum] at h
  simpa only [div_eq_mul_inv, mul_comm (n : ℝ)⁻¹] using h

theorem sum_le_of_moment_bound (n s t : ℕ) (hn : 0 < n) (hs : 1 ≤ s)
    (ht : 1 ≤ t) (x : Fin n → ℝ) (hx : ∀ v, 0 ≤ x v)
    (hmoment : ∑ v, x v ^ s ≤ (t : ℝ) ^ s * (n : ℝ) ^ s) :
    (∑ v, x v) ≤ (t : ℝ) * (n : ℝ) ^ (2 - 1 / (s : ℝ)) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hn0 := hnpos.ne'
  have hspos : (0 : ℝ) < s := by exact_mod_cast (show 0 < s by omega)
  have hs0 := hspos.ne'
  have hmean := (mean_pow_le n s hn x hx).trans
    (div_le_div_of_nonneg_right hmoment hnpos.le)
  have hpower : ((t : ℝ) * (n : ℝ) ^ (1 - 1 / (s : ℝ))) ^ s =
      ((t : ℝ) ^ s * (n : ℝ) ^ s) / n := by
    rw [mul_pow, ← Real.rpow_mul_natCast hnpos.le]
    have hexp : (1 - 1 / (s : ℝ)) * s = (s : ℝ) - 1 := by field_simp
    rw [hexp, Real.rpow_sub hnpos, Real.rpow_natCast, Real.rpow_one]
    ring
  have havg : (∑ v, x v) / n ≤ (t : ℝ) * (n : ℝ) ^ (1 - 1 / (s : ℝ)) := by
    apply (pow_le_pow_iff_left₀
      (div_nonneg (sum_nonneg (fun v _ => hx v)) hnpos.le)
      (by positivity) (show s ≠ 0 by omega)).mp
    exact hmean.trans_eq hpower.symm
  have hmul := (div_le_iff₀ hnpos).mp havg
  calc
    (∑ v, x v) ≤ (t : ℝ) * (n : ℝ) ^ (1 - 1 / (s : ℝ)) * n := hmul
    _ = (t : ℝ) * ((n : ℝ) ^ (1 - 1 / (s : ℝ)) * (n : ℝ) ^ (1 : ℝ)) := by
      rw [Real.rpow_one, mul_assoc]
    _ = (t : ℝ) * (n : ℝ) ^ (2 - 1 / (s : ℝ)) := by
      rw [← Real.rpow_add hnpos]
      congr 2
      ring

end
-- Source module: Main.lean
open Finset

theorem solution (s t : ℕ) (hs : 2 ≤ s) (ht : 2 ≤ t) :
    ∀ eps : ℝ, 0 < eps →
    ∃ C : ℝ, 0 < C ∧
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (¬∃ (A B : Finset (Fin n)), A.card = s ∧ B.card = t ∧
        ∀ a ∈ A, ∀ b ∈ B, G.Adj a b) →
      G.edgeFinset.card ≤ C * n ^ (2 - 1/s + eps) := by
  intro eps heps
  refine ⟨(s : ℝ) + t, by positivity, ?_⟩
  intro n G _ hfree
  by_cases hn : n = 0
  · subst n
    have hzero : G.edgeFinset.card = 0 := by
      have h := G.sum_degrees_eq_twice_card_edges
      simp only [univ_eq_empty, sum_empty] at h
      omega
    rw [hzero, Nat.cast_zero]
    exact mul_nonneg (by positivity) (Real.rpow_nonneg (by positivity) _)
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hnpos
  have hs1 : 1 ≤ s := by omega
  have ht1 : 1 ≤ t := by omega
  have hcount := sum_choose_degree_le_fin G s t ht1 hfree
  have hshift := shifted_moment_bound n s t (fun v => G.degree v) hcount
  have ht_power : t - 1 ≤ t ^ s :=
    (Nat.sub_le t 1).trans (le_self_pow₀ ht1 (by omega))
  have hmomentNat : ∑ v : Fin n, (G.degree v + 1 - s) ^ s ≤ t ^ s * n ^ s :=
    hshift.trans (Nat.mul_le_mul_right _ ht_power)
  have hmoment : ∑ v : Fin n, ((G.degree v + 1 - s : ℕ) : ℝ) ^ s ≤
      (t : ℝ) ^ s * (n : ℝ) ^ s := by exact_mod_cast hmomentNat
  have hsum := sum_le_of_moment_bound n s t hnpos hs1 ht1
    (fun v => ((G.degree v + 1 - s : ℕ) : ℝ)) (fun _ => by positivity) hmoment
  have hdegrees : ∑ v : Fin n, G.degree v ≤
      (∑ v : Fin n, (G.degree v + 1 - s)) + n * (s - 1) := by
    calc
      ∑ v : Fin n, G.degree v ≤ ∑ v : Fin n, ((G.degree v + 1 - s) + (s - 1)) := by
        apply sum_le_sum
        intro v _
        omega
      _ = _ := by simp [sum_add_distrib]
  have hdegreesReal : (∑ v : Fin n, (G.degree v : ℝ)) ≤
      (∑ v : Fin n, ((G.degree v + 1 - s : ℕ) : ℝ)) + (n : ℝ) * (s - 1 : ℕ) := by
    exact_mod_cast hdegrees
  have hsreal : (1 : ℝ) ≤ s := by exact_mod_cast hs1
  have hexp : 1 ≤ 2 - 1 / (s : ℝ) := by
    have hrecip : 1 / (s : ℝ) ≤ 1 := by
      simpa only [div_one] using
        one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hsreal
    linarith only [hrecip]
  have hn_power : (n : ℝ) ≤ (n : ℝ) ^ (2 - 1 / (s : ℝ)) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hn1 hexp
  have hcorrection : (n : ℝ) * (s - 1 : ℕ) ≤
      (s : ℝ) * (n : ℝ) ^ (2 - 1 / (s : ℝ)) := by
    calc
      (n : ℝ) * (s - 1 : ℕ) ≤ (n : ℝ) * s := by
        exact mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.sub_le s 1) (by positivity)
      _ ≤ (s : ℝ) * (n : ℝ) ^ (2 - 1 / (s : ℝ)) := by
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_left hn_power (by positivity)
  have hhand : (∑ v : Fin n, (G.degree v : ℝ)) = 2 * (G.edgeFinset.card : ℝ) := by
    exact_mod_cast G.sum_degrees_eq_twice_card_edges
  have hbase : (G.edgeFinset.card : ℝ) ≤
      ((s : ℝ) + t) * (n : ℝ) ^ (2 - 1 / (s : ℝ)) := by
    rw [hhand] at hdegreesReal
    have hedge : (0 : ℝ) ≤ G.edgeFinset.card := by positivity
    nlinarith
  exact hbase.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)) (by positivity))

#check @solution
#print axioms solution
