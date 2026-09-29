-- Prove2me | solution 1 for Catalog.Combinatorics.HybridEvictionAdditiveLaw.sum_le_sum_of_sdiff_dominated
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T00:15:36.517389+00:00
-- url     : https://prove2.me/submissions/296c7a3e-601a-4942-9096-439279360f16

import Mathlib
import Definitions.Def_Combinatorics_HybridEvictionAdditiveLaw
open Finset Catalog.Combinatorics.HybridEvictionAdditiveLaw in
theorem solution {ι : Type*} [DecidableEq ι] (v : ι → ℝ) {S T : Finset ι}
    (hcard : T.card = S.card)
    (hdom : ∀ j ∈ T \ S, ∀ i ∈ S \ T, v j ≤ v i) :
    retained v T ≤ retained v S := by
  unfold retained
  -- both sets share `S ∩ T`; the exchanged parts have the same size
  rw [← sum_inter_add_sum_diff T S v, ← sum_inter_add_sum_diff S T v, inter_comm T S]
  have hc : (T \ S).card = (S \ T).card := by
    have h1 := card_sdiff_add_card_inter T S
    have h2 := card_sdiff_add_card_inter S T
    rw [inter_comm] at h2
    omega
  suffices hsd : ∑ x ∈ T \ S, v x ≤ ∑ x ∈ S \ T, v x by linarith
  rcases (S \ T).eq_empty_or_nonempty with he | hne
  · have : T \ S = ∅ := card_eq_zero.1 (by rw [hc, he, card_empty])
    rw [this, he]
  · -- every exchanged-in value is below the minimum `m` of the exchanged-out values
    set m := (S \ T).inf' hne v with hm
    calc ∑ x ∈ T \ S, v x ≤ ∑ x ∈ T \ S, m :=
          sum_le_sum (fun j hj => le_inf' hne v (fun i hi => hdom j hj i hi))
      _ = (S \ T).card * m := by rw [sum_const, hc, nsmul_eq_mul]
      _ = ∑ x ∈ S \ T, m := by rw [sum_const, nsmul_eq_mul]
      _ ≤ ∑ x ∈ S \ T, v x := sum_le_sum (fun i hi => inf'_le v hi)
