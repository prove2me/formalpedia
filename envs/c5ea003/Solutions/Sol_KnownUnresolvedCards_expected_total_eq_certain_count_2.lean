-- Prove2me | solution 2 for KnownUnresolvedCards.expected_total_eq_certain_count
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T21:26:08.748542+00:00
-- url     : https://prove2.me/submissions/597abb5e-9c6d-4ceb-b6e6-157ade5b8e20

import Definitions.Def_MachineLearning_KnownUnresolvedCards_Basic
open KnownUnresolvedCards in
theorem solution {Ω : Type*} [Fintype Ω] {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty Ω]
    (p : ι → Ω → ℚ) (K : Finset ι)
    (hK : ∀ i ∈ K, Resolved (p i) 1)
    (hU : ∀ i ∉ K, Fair (p i)) :
    E (fun ω => ∑ i, p i ω) = (K.card : ℚ) := by
  have hΩ : (Fintype.card Ω : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_pos.ne'
  have hsum : E (fun ω => ∑ i, p i ω) = ∑ i, E (p i) := by
    unfold E
    rw [Finset.sum_comm, Finset.sum_div]
  have hterm : ∀ i, E (p i) = if i ∈ K then 1 else 0 := by
    intro i
    split_ifs with hi
    · have hr : ∀ ω, p i ω = 1 := hK i hi
      unfold E
      simp only [hr, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
      exact div_self hΩ
    · exact hU i hi
  rw [hsum]
  simp only [hterm, Finset.sum_boole]
  simp
