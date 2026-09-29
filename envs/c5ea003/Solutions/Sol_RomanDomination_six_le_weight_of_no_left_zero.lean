-- Prove2me | solution 1 for RomanDomination.six_le_weight_of_no_left_zero
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T15:02:42.708516+00:00
-- url     : https://prove2.me/submissions/de7f427d-f68a-4996-a528-9c1b19feccef

import Mathlib
import Definitions.Def_Geometry_RomanDomination_ConvexBipartite
import Definitions.Def_Geometry_RomanDomination_DoubleRoman
import Definitions.Def_Geometry_RomanDomination_Variants
open RomanDomination Finset in
theorem solution {m n : ℕ} {f : Fin m ⊕ Fin n → ℕ} (hm : 3 ≤ m) (hn : 3 ≤ n)
    (hf : IsDRDF (K m n) f) (hb : 2 ≤ ∑ j, f (Sum.inr j)) (h0 : ∀ i, f (Sum.inl i) ≠ 0) :
    6 ≤ weight f := by
  have hw : weight f = ∑ i, f (Sum.inl i) + ∑ j, f (Sum.inr j) := Fintype.sum_sum_type f
  by_cases hA4 : 4 ≤ ∑ i, f (Sum.inl i)
  · omega
  · -- left sum `≤ 3` with `m ≥ 3` nonzero labels: every left label is `1`
    have hle : ∀ i, f (Sum.inl i) ≤ 1 := by
      intro i
      have hsplit := Finset.add_sum_erase Finset.univ (fun i => f (Sum.inl i)) (Finset.mem_univ i)
      have hrest : m - 1 ≤ ∑ i' ∈ Finset.univ.erase i, f (Sum.inl i') := by
        calc m - 1 = ∑ _i' ∈ Finset.univ.erase i, 1 := by
              rw [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_erase_of_mem (Finset.mem_univ i),
                Finset.card_univ, Fintype.card_fin]
          _ ≤ ∑ i' ∈ Finset.univ.erase i, f (Sum.inl i') :=
              Finset.sum_le_sum fun i' _ => Nat.one_le_iff_ne_zero.mpr (h0 i')
      simp only at hsplit
      omega
    -- hence every right label is at least `2`
    have hright : ∀ j, 2 ≤ f (Sum.inr j) := by
      intro j
      by_contra hlt
      push Not at hlt
      rcases Nat.lt_succ_iff.mp hlt |>.lt_or_eq with h0' | h1
      · have h0'' : f (Sum.inr j) = 0 := by omega
        rcases hf.2.1 (Sum.inr j) h0'' with ⟨u, hadj, hu⟩ | ⟨u, w, -, hu, -, hu2, -⟩
        · cases u with
          | inl i => have := hle i; omega
          | inr j' => simp at hadj
        · cases u with
          | inl i => have := hle i; omega
          | inr j' => simp at hu
      · obtain ⟨u, hadj, hu⟩ := hf.2.2 (Sum.inr j) h1
        cases u with
        | inl i => have := hle i; omega
        | inr j' => simp at hadj
    have hB : 2 * n ≤ ∑ j, f (Sum.inr j) := by
      calc 2 * n = ∑ _j : Fin n, 2 := by simp [mul_comm]
        _ ≤ ∑ j, f (Sum.inr j) := Finset.sum_le_sum fun j _ => hright j
    omega
