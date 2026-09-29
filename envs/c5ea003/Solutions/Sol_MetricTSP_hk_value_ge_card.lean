-- Prove2me | solution 1 for MetricTSP.hk_value_ge_card
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-24T20:14:13.054497+00:00
-- url     : https://prove2.me/submissions/adc7b75e-5b94-4ffc-b041-6fb872cc883b

import Mathlib
import Definitions.Def_MetricTSP_model
import Definitions.Def_MetricTSP_tour_vector
import Theorems.Thm_MetricTSP_tour_vector_held_karp

namespace MetricTSP

theorem hk_ge_card (n : ℕ) (hn : 3 ≤ n) (c : Fin n → Fin n → ℝ)
    (hc1 : ∀ u v, u ≠ v → 1 ≤ c u v) : (n : ℝ) ≤ hkValue c := by
  unfold hkValue
  apply le_csInf
  · exact ⟨(1 / 2) * ∑ u, ∑ v, c u v * tourVec 1 u v, tourVec 1,
      tour_vector_held_karp n hn 1, rfl⟩
  · rintro t ⟨x, hx, rfl⟩
    have hxnn : ∀ u v, 0 ≤ x u v := hx.2.2.1
    have hxdiag : ∀ v, x v v = 0 := hx.2.1
    have hxdeg : ∀ v, ∑ u, x v u = 2 := hx.2.2.2.2.1
    have hterm : ∀ u v : Fin n, x u v ≤ c u v * x u v := by
      intro u v
      by_cases huv : u = v
      · subst huv
        rw [hxdiag u]
        simp
      · have h1 := hc1 u v huv
        have h0 := hxnn u v
        nlinarith
    have hsum : ∑ u, ∑ v, x u v ≤ ∑ u, ∑ v, c u v * x u v := by
      apply Finset.sum_le_sum
      intro u _
      apply Finset.sum_le_sum
      intro v _
      exact hterm u v
    have htotal : ∑ u : Fin n, ∑ v : Fin n, x u v = 2 * n := by
      rw [Finset.sum_congr rfl (fun u (_ : u ∈ Finset.univ) => hxdeg u)]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    rw [htotal] at hsum
    linarith

end MetricTSP

open MetricTSP

theorem solution (n : ℕ) (hn : 3 ≤ n) (c : Fin n → Fin n → ℝ)
    (hc1 : ∀ u v, u ≠ v → 1 ≤ c u v) : (n : ℝ) ≤ hkValue c :=
  MetricTSP.hk_ge_card n hn c hc1
