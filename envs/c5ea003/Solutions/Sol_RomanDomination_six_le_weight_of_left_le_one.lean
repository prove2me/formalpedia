-- Prove2me | solution 1 for RomanDomination.six_le_weight_of_left_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T14:43:51.547848+00:00
-- url     : https://prove2.me/submissions/4480e52d-2c86-409d-8de2-80b619bdd247

import Mathlib
import Definitions.Def_Geometry_RomanDomination_ConvexBipartite
import Definitions.Def_Geometry_RomanDomination_DoubleRoman
import Definitions.Def_Geometry_RomanDomination_Variants
open RomanDomination Finset in
theorem solution {m n : ℕ} {f : Fin m ⊕ Fin n → ℕ} (hn : 3 ≤ n) (hf : IsDRDF (K m n) f)
    (ha : ∑ i, f (Sum.inl i) ≤ 1) : 6 ≤ weight f := by
  -- every left label is at most `1`
  have hle : ∀ i, f (Sum.inl i) ≤ 1 := fun i =>
    (Finset.single_le_sum (f := fun i => f (Sum.inl i)) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ i)).trans ha
  -- so no right vertex can be labelled `0` or `1`: its neighbours are all on the left
  have hright : ∀ j, 2 ≤ f (Sum.inr j) := by
    intro j
    by_contra hlt
    push Not at hlt
    rcases Nat.lt_succ_iff.mp hlt |>.lt_or_eq with h0 | h1
    · have h0' : f (Sum.inr j) = 0 := by omega
      rcases hf.2.1 (Sum.inr j) h0' with ⟨u, hadj, hu⟩ | ⟨u, w, -, hu, -, hu2, -⟩
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
  have hw : weight f = ∑ i, f (Sum.inl i) + ∑ j, f (Sum.inr j) := Fintype.sum_sum_type f
  omega
