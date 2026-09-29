-- Prove2me | solution 2 for KnownUnresolvedCards.expected_total_eq_certain_sum
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T01:04:19.847522+00:00
-- url     : https://prove2.me/submissions/214b345a-e39f-4334-a7ec-f90a14cde27b

import Definitions.Def_MachineLearning_KnownUnresolvedCards_Basic
open KnownUnresolvedCards in
theorem solution {Ω : Type*} [Fintype Ω] {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty Ω]
    (p : ι → Ω → ℚ) (K : Finset ι) (c : ι → ℚ)
    (hK : ∀ i ∈ K, Resolved (p i) (c i))
    (hU : ∀ i ∉ K, Fair (p i)) :
    E (fun ω => ∑ i, p i ω) = ∑ i ∈ K, c i := by
  have hΩ : (Fintype.card Ω : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_pos.ne'
  have hsum : E (fun ω => ∑ i, p i ω) = ∑ i, E (p i) := by
    unfold E
    rw [Finset.sum_comm, Finset.sum_div]
  have hterm : ∀ i, E (p i) = if i ∈ K then c i else 0 := by
    intro i
    split_ifs with hi
    · have hr : ∀ ω, p i ω = (c i) := hK i hi
      unfold E
      simp only [hr, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      field_simp
    · exact hU i hi
  rw [hsum]
  simp only [hterm]
  rw [Finset.sum_ite_mem, Finset.univ_inter]
