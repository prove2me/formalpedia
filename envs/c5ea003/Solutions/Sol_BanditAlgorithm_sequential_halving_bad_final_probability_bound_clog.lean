-- Prove2me | solution 1 for BanditAlgorithm.sequential_halving_bad_final_probability_bound_clog
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-02T16:40:31.363097+00:00
-- url     : https://prove2.me/submissions/d53b6282-1abc-4f86-b9af-97b3afccf787

import Theorems.Thm_BanditAlgorithm_sequential_halving_last_optimal_elimination_probability_bound_clog

open MeasureTheory Finset
open BanditAlgorithm

private lemma exists_transition_of_true_not_final (P : ℕ → Prop) [DecidablePred P]
    (L : ℕ) (hzero : P 0) (hfinal : ¬ P L) :
    ∃ ℓ < L, P ℓ ∧ ¬ P (ℓ + 1) := by
  induction L with
  | zero => exact (hfinal hzero).elim
  | succ L ih =>
      by_cases hprev : P L
      · exact ⟨L, Nat.lt_succ_self L, hprev, hfinal⟩
      · rcases ih hprev with ⟨ℓ, hℓ, hp, hn⟩
        exact ⟨ℓ, hℓ.trans (Nat.lt_succ_self L), hp, hn⟩

theorem solution {k n : ℕ}
    (ν : StochasticBandit k) (hν : IsSubgaussianBandit 1 ν)
    (hsorted : ∀ i j : Fin k, i ≤ j → banditArmMean ν j ≤ banditArmMean ν i)
    (hn : k * Nat.clog 2 k ≤ n) (H₂ : ℝ)
    (hH₂ : ∀ i : Fin k, 0 < banditGap ν i →
      ((i : ℕ) + 1 : ℝ) / banditGap ν i ^ 2 ≤ H₂)
    (π : BanditPolicy k) :
    (banditMeasure ν π n).real {h | IsSeqHalvingBadFinalRun k n ν h} ≤
      3 * (Nat.clog 2 k : ℝ) *
        Real.exp (-(n / (16 * H₂ * (Nat.clog 2 k : ℝ)))) := by
  classical
  let L := Nat.clog 2 k
  let μ := banditMeasure ν π n
  let E : Fin L → Set (BanditHistory k n) := fun ℓ ↦
    {h | IsSeqHalvingLastOptimalEliminationAt k n ν h (ℓ : ℕ)}
  have hgap_nonneg (i : Fin k) : 0 ≤ banditGap ν i := by
    rw [banditGap]
    exact sub_nonneg.mpr
      (le_ciSup (Set.finite_range (fun j : Fin k ↦ banditArmMean ν j)).bddAbove i)
  have hsubset : {h | IsSeqHalvingBadFinalRun k n ν h} ⊆ ⋃ ℓ : Fin L, E ℓ := by
    intro h hh
    rcases hh with ⟨A, hA0, hA, hoptzero, hfinal⟩
    let P : ℕ → Prop := fun s ↦ ∃ i ∈ A s, banditGap ν i = 0
    have hnotfinal : ¬ P L := by
      rintro ⟨i, hi, hgap⟩
      have := hfinal i hi
      linarith
    rcases exists_transition_of_true_not_final P L hoptzero hnotfinal with
      ⟨ℓ, hℓ, hopt, hnone⟩
    apply Set.mem_iUnion.2
    refine ⟨⟨ℓ, hℓ⟩, A, hA0, hA, hopt, ?_⟩
    intro i hi
    have hne : banditGap ν i ≠ 0 := by
      intro heq
      exact hnone ⟨i, hi, heq⟩
    exact lt_of_le_of_ne (hgap_nonneg i) (Ne.symm hne)
  calc
    μ.real {h | IsSeqHalvingBadFinalRun k n ν h} ≤ μ.real (⋃ ℓ : Fin L, E ℓ) :=
      measureReal_mono hsubset
    _ ≤ ∑ ℓ : Fin L, μ.real (E ℓ) := measureReal_iUnion_fintype_le E
    _ ≤ ∑ _ℓ : Fin L,
        3 * Real.exp (-(n / (16 * H₂ * (Nat.clog 2 k : ℝ)))) := by
      apply Finset.sum_le_sum
      intro ℓ _hℓ
      exact sequential_halving_last_optimal_elimination_probability_bound_clog
        ν hν hsorted hn H₂ hH₂ π ℓ (by simpa [L] using ℓ.isLt)
    _ = 3 * (Nat.clog 2 k : ℝ) *
        Real.exp (-(n / (16 * H₂ * (Nat.clog 2 k : ℝ)))) := by
      simp [L]
      ring
