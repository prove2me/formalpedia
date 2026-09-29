-- Prove2me | solution 1 for MarkovMixing.cftp_coalescence
-- status  : ACCEPTED   (prove)
-- author  : @MKPynnic
-- created : 2026-08-22T18:41:21.409635+00:00
-- url     : https://prove2.me/submissions/b5b18c97-6667-4efd-991f-e7a8a28a05a8

import Definitions.Def_mm_cftp
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.OfFn

/-!
# CFTP coalesces almost surely

Let `q_s` be the probability that `s` i.i.d. update maps have not yet
composed to a constant map.

* **Submultiplicativity.** Splitting a tuple of length `a+b` into its two
  blocks (`Fin.appendEquiv`), the composition factors as
  `F_{a+b} = F_a ∘ F_b`; if *either* block is already constant so is the
  whole composition.  Hence non-coalescence of the whole forces
  non-coalescence of both blocks, and `q_{a+b} ≤ q_a q_b`.
* **A single good block.** The hypothesis provides one tuple of length `t`
  of positive probability `p` that already coalesces, and the total mass of
  all tuples is `1`, so `q_t ≤ 1 − p < 1`.

Together these give `q_s ≤ q_{⌊s/t⌋ t} ≤ (1−p)^{⌊s/t⌋} → 0`.  (The
degenerate case `t = 0` means the state space is a single point, where
`q_s = 0` outright.)
-/

namespace MarkovMixing

open scoped BigOperators

private lemma cftpCompose_append {V : Type*} [Fintype V] [DecidableEq V] {a b : ℕ}
    (G : Fin a → (V → V)) (H : Fin b → (V → V)) (x : V) :
    cftpCompose (Fin.append G H) x = cftpCompose G (cftpCompose H x) := by
  simp [cftpCompose, List.ofFn_fin_append, List.foldr_append]

private lemma weight_nonneg {V : Type*} [Fintype V] [DecidableEq V]
    {ν : (V → V) → ℝ} (hν : IsDist ν) {s : ℕ} (F : Fin s → (V → V)) :
    (0 : ℝ) ≤ ∏ i, ν (F i) :=
  Finset.prod_nonneg fun i _ => hν.1 (F i)

private lemma total_mass {V : Type*} [Fintype V] [DecidableEq V]
    {ν : (V → V) → ℝ} (hν : IsDist ν) (s : ℕ) :
    ∑ F : Fin s → (V → V), ∏ i, ν (F i) = 1 := by
  classical
  have h := Finset.prod_univ_sum (fun _ : Fin s => (Finset.univ : Finset (V → V)))
    (fun (_ : Fin s) (f : V → V) => ν f)
  simp only [Fintype.piFinset_univ, hν.2, Finset.prod_const_one] at h
  exact h.symm

private lemma notCoal_nonneg {V : Type*} [Fintype V] [DecidableEq V]
    {ν : (V → V) → ℝ} (hν : IsDist ν) (s : ℕ) : 0 ≤ cftpNotCoalescedProb ν s := by
  refine Finset.sum_nonneg fun F _ => ?_
  by_cases h : ∀ x y : V, cftpCompose F x = cftpCompose F y
  · rw [if_neg (not_not_intro h)]
  · rw [if_pos h]
    exact weight_nonneg hν F

private lemma notCoal_le_one {V : Type*} [Fintype V] [DecidableEq V]
    {ν : (V → V) → ℝ} (hν : IsDist ν) (s : ℕ) : cftpNotCoalescedProb ν s ≤ 1 := by
  rw [← total_mass hν s]
  refine Finset.sum_le_sum fun F _ => ?_
  by_cases h : ∀ x y : V, cftpCompose F x = cftpCompose F y
  · rw [if_neg (not_not_intro h)]
    exact weight_nonneg hν F
  · rw [if_pos h]

private lemma notCoal_submul {V : Type*} [Fintype V] [DecidableEq V]
    {ν : (V → V) → ℝ} (hν : IsDist ν) (a b : ℕ) :
    cftpNotCoalescedProb ν (a + b) ≤ cftpNotCoalescedProb ν a * cftpNotCoalescedProb ν b := by
  classical
  have hsplit : cftpNotCoalescedProb ν (a + b)
      = ∑ G : Fin a → (V → V), ∑ H : Fin b → (V → V),
          (if ¬∀ x y : V, cftpCompose (Fin.append G H) x = cftpCompose (Fin.append G H) y then
            (∏ i, ν (G i)) * ∏ j, ν (H j) else 0) := by
    rw [cftpNotCoalescedProb,
      ← Equiv.sum_comp (Fin.appendEquiv (α := V → V) a b)
        (fun F : Fin (a + b) → (V → V) =>
          if ¬∀ x y : V, cftpCompose F x = cftpCompose F y then ∏ i, ν (F i) else 0),
      Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun G _ => Finset.sum_congr rfl fun H _ => ?_
    have hprod : ∏ i : Fin (a + b), ν (Fin.append G H i)
        = (∏ i, ν (G i)) * ∏ j, ν (H j) := by
      rw [Fin.prod_univ_add]
      simp
    have happ : (Fin.appendEquiv (α := V → V) a b) (G, H) = Fin.append G H := rfl
    rw [happ, hprod]
  rw [hsplit, cftpNotCoalescedProb, cftpNotCoalescedProb, Finset.sum_mul]
  refine Finset.sum_le_sum fun G _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun H _ => ?_
  by_cases hG : ∀ x y : V, cftpCompose G x = cftpCompose G y
  · have hA : ∀ x y : V,
        cftpCompose (Fin.append G H) x = cftpCompose (Fin.append G H) y := by
      intro x y
      rw [cftpCompose_append, cftpCompose_append]
      exact hG _ _
    rw [if_neg (not_not_intro hA), if_neg (not_not_intro hG), zero_mul]
  · by_cases hH : ∀ x y : V, cftpCompose H x = cftpCompose H y
    · have hA : ∀ x y : V,
          cftpCompose (Fin.append G H) x = cftpCompose (Fin.append G H) y := by
        intro x y
        rw [cftpCompose_append, cftpCompose_append, hH x y]
      rw [if_neg (not_not_intro hA), if_neg (not_not_intro hH), mul_zero]
    · rw [if_pos hG, if_pos hH]
      by_cases hA : ¬∀ x y : V,
          cftpCompose (Fin.append G H) x = cftpCompose (Fin.append G H) y
      · rw [if_pos hA]
      · rw [if_neg hA]
        exact mul_nonneg (weight_nonneg hν G) (weight_nonneg hν H)

private lemma notCoal_antitone {V : Type*} [Fintype V] [DecidableEq V]
    {ν : (V → V) → ℝ} (hν : IsDist ν) {s s' : ℕ} (h : s ≤ s') :
    cftpNotCoalescedProb ν s' ≤ cftpNotCoalescedProb ν s := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  calc cftpNotCoalescedProb ν (s + d)
      ≤ cftpNotCoalescedProb ν s * cftpNotCoalescedProb ν d := notCoal_submul hν s d
    _ ≤ cftpNotCoalescedProb ν s * 1 :=
        mul_le_mul_of_nonneg_left (notCoal_le_one hν d) (notCoal_nonneg hν s)
    _ = cftpNotCoalescedProb ν s := mul_one _

private lemma notCoal_pow {V : Type*} [Fintype V] [DecidableEq V]
    {ν : (V → V) → ℝ} (hν : IsDist ν) (t m : ℕ) :
    cftpNotCoalescedProb ν (m * t) ≤ cftpNotCoalescedProb ν t ^ m := by
  induction m with
  | zero => simpa using notCoal_le_one hν 0
  | succ n ih =>
      have h : (n + 1) * t = n * t + t := by ring
      rw [h, pow_succ]
      calc cftpNotCoalescedProb ν (n * t + t)
          ≤ cftpNotCoalescedProb ν (n * t) * cftpNotCoalescedProb ν t := notCoal_submul hν _ _
        _ ≤ cftpNotCoalescedProb ν t ^ n * cftpNotCoalescedProb ν t :=
            mul_le_mul_of_nonneg_right ih (notCoal_nonneg hν t)

private lemma notCoal_le_one_sub {V : Type*} [Fintype V] [DecidableEq V]
    {ν : (V → V) → ℝ} (hν : IsDist ν) {t : ℕ} (F₀ : Fin t → (V → V))
    (hc : ∀ x y : V, cftpCompose F₀ x = cftpCompose F₀ y) :
    cftpNotCoalescedProb ν t ≤ 1 - ∏ i, ν (F₀ i) := by
  classical
  have hkey : cftpNotCoalescedProb ν t
      ≤ ∑ F : Fin t → (V → V), ((∏ i, ν (F i)) - (if F = F₀ then ∏ i, ν (F i) else 0)) := by
    refine Finset.sum_le_sum fun F _ => ?_
    by_cases hF : F = F₀
    · subst hF
      rw [if_pos rfl, sub_self, if_neg (not_not_intro hc)]
    · rw [if_neg hF, sub_zero]
      by_cases h : ∀ x y : V, cftpCompose F x = cftpCompose F y
      · rw [if_neg (not_not_intro h)]
        exact weight_nonneg hν F
      · rw [if_pos h]
  refine le_trans hkey ?_
  rw [Finset.sum_sub_distrib, total_mass hν t,
    Finset.sum_ite_eq' Finset.univ F₀ (fun F : Fin t → (V → V) => ∏ i, ν (F i))]
  simp

end MarkovMixing

open MarkovMixing

/-- **LPW §22.3**: if some finite sequence of update maps of positive
probability coalesces, then the CFTP non-coalescence probability tends to
zero. -/
theorem solution {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (P : Matrix V V ℝ) (hP : IsStochastic P)
    (ν : (V → V) → ℝ) (hν : IsRandomMapRep P ν)
    (hpos : ∃ (t : ℕ) (F : Fin t → (V → V)),
      0 < ∏ i, ν (F i) ∧ ∀ x y : V, cftpCompose F x = cftpCompose F y) :
    Filter.Tendsto (fun t => cftpNotCoalescedProb ν t)
      Filter.atTop (nhds 0) := by
  obtain ⟨t, F₀, hp, hc⟩ := hpos
  have hd : IsDist ν := hν.1
  rcases Nat.eq_zero_or_pos t with ht | ht
  · subst ht
    have hq0 : cftpNotCoalescedProb ν 0 ≤ 0 := by
      have h := notCoal_le_one_sub hd F₀ hc
      have hp1 : ∏ i : Fin 0, ν (F₀ i) = 1 := by simp
      rw [hp1] at h
      simpa using h
    have hall : ∀ s : ℕ, cftpNotCoalescedProb ν s = 0 := by
      intro s
      have h1 := notCoal_antitone hd (Nat.zero_le s)
      have h2 := notCoal_nonneg hd s
      linarith
    simp only [hall]
    exact tendsto_const_nhds
  · have hqt : cftpNotCoalescedProb ν t ≤ 1 - ∏ i, ν (F₀ i) := notCoal_le_one_sub hd F₀ hc
    have hr0 : (0 : ℝ) ≤ 1 - ∏ i, ν (F₀ i) := le_trans (notCoal_nonneg hd t) hqt
    have hr1 : (1 : ℝ) - ∏ i, ν (F₀ i) < 1 := by linarith
    have hbound : ∀ s : ℕ,
        cftpNotCoalescedProb ν s ≤ (1 - ∏ i, ν (F₀ i)) ^ (s / t) := by
      intro s
      calc cftpNotCoalescedProb ν s ≤ cftpNotCoalescedProb ν ((s / t) * t) :=
            notCoal_antitone hd (Nat.div_mul_le_self s t)
        _ ≤ cftpNotCoalescedProb ν t ^ (s / t) := notCoal_pow hd t (s / t)
        _ ≤ (1 - ∏ i, ν (F₀ i)) ^ (s / t) :=
            pow_le_pow_left₀ (notCoal_nonneg hd t) hqt _
    have hdiv : Filter.Tendsto (fun s : ℕ => s / t) Filter.atTop Filter.atTop := by
      refine Filter.tendsto_atTop_atTop.mpr fun N => ⟨N * t, fun s hs => ?_⟩
      exact (Nat.le_div_iff_mul_le ht).mpr hs
    have hpow : Filter.Tendsto (fun s : ℕ => (1 - ∏ i, ν (F₀ i)) ^ (s / t))
        Filter.atTop (nhds 0) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).comp hdiv
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hpow
      (fun s => notCoal_nonneg hd s) hbound
