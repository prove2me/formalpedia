-- Prove2me | solution 1 for mme_complete_split_112_exact_address_histogram
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-06T21:47:01.77029+00:00
-- url     : https://prove2.me/submissions/ca2d106b-620a-4caa-a49b-cd5c7c4a59e6

import Definitions.Def_mme_complete_split_112_address_words
import Definitions.Def_mme_more_asymmetry_first_112_profile_data
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096

open MME MME.CompleteSplit112 BigOperators

private theorem count_as_sum (N L G : ℕ)
    (address : CWQ6ExactCoupledAddress N L G)
    (mode : Fin 3) (word : Fin 2 → Fin 3) :
    Fintype.card {r : Fin (2 * N) // fineWord mode (address.1 mode r) = word} =
      ∑ grade : Fin 3,
        if fineWord mode grade = word then
          cwQ6CoupledMarginalMultiplicity N L G mode grade else 0 := by
  rw [Fintype.card_subtype]
  let grades := Finset.univ.filter (fun grade : Fin 3 ↦ fineWord mode grade = word)
  have h := Finset.sum_card_fiberwise_eq_card_filter
    (Finset.univ : Finset (Fin (2 * N))) grades (address.1 mode)
  calc
    _ = ∑ grade ∈ grades,
        (Finset.univ.filter (fun r : Fin (2 * N) ↦ address.1 mode r = grade)).card := by
      simpa [grades] using h.symm
    _ = ∑ grade ∈ grades, cwQ6CoupledMarginalMultiplicity N L G mode grade := by
      apply Finset.sum_congr rfl
      intro grade _
      exact address.2.2 mode grade
    _ = _ := by rw [Finset.sum_filter]

private theorem general_histogram (N L G : ℕ) (p : ℚ)
    (hLG : L + G = N) (hLp : (L : ℚ) = (2 * N : ℕ) * p)
    (address : CWQ6ExactCoupledAddress N L G)
    (mode : Fin 3) (word : Fin 2 → Fin 3) :
    (Fintype.card {r : Fin (2 * N) // fineWord mode (address.1 mode r) = word} : ℚ) =
      (2 * N : ℕ) * profileProbability p mode word := by
  rw [count_as_sum]
  have hLGq : (L : ℚ) + G = N := by exact_mod_cast hLG
  have hw : word = ![word 0, word 1] := by
    ext j
    fin_cases j <;> rfl
  rw [hw]
  generalize word 0 = a
  generalize word 1 = b
  fin_cases mode <;> fin_cases a <;> fin_cases b <;>
    norm_num [Fin.sum_univ_succ, fineWord, profileProbability,
      cwQ6CoupledMarginalMultiplicity] <;>
    push_cast at hLp ⊢ <;> nlinarith

theorem solution :
    (∀ (N L G : ℕ) (p : ℚ), L + G = N →
      (L : ℚ) = (2 * N : ℕ) * p →
      ∀ (address : CWQ6ExactCoupledAddress N L G)
        (mode : Fin 3) (word : Fin 2 → Fin 3),
        (Fintype.card {r : Fin (2 * N) //
          fineWord mode (address.1 mode r) = word} : ℚ) =
          (2 * N : ℕ) * profileProbability p mode word) ∧
    (∀ (m : ℕ)
      (address : CWQ6ExactCoupledAddress
        (1180591620717411303424 * m)
        (8959763742786037 * m)
        (1180582660953668517387 * m))
      (mode : Fin 3) (word : Fin 2 → Fin 3),
      (Fintype.card {r : Fin (2 * (1180591620717411303424 * m)) //
        fineWord mode (address.1 mode r) = word} : ℝ) =
        (2 * (1180591620717411303424 * m) : ℕ) *
          (MoreAsymmetryFirstSlice.probability 0 mode word : ℝ)) := by
  constructor
  · exact general_histogram
  · intro m address mode word
    have h := general_histogram
      (1180591620717411303424 * m)
      (8959763742786037 * m)
      (1180582660953668517387 * m)
      MoreAsymmetryFirstSlice.split0
      (by omega)
      (by norm_num [MoreAsymmetryFirstSlice.split0]; ring)
      address mode word
    have heq : profileProbability MoreAsymmetryFirstSlice.split0 mode word =
        MoreAsymmetryFirstSlice.probability 0 mode word := by
      simp [profileProbability, MoreAsymmetryFirstSlice.probability,
        MoreAsymmetryFirstSlice.baseProbability]
    rw [heq] at h
    exact_mod_cast h

