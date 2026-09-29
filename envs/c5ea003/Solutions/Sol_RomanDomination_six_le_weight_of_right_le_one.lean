-- Prove2me | solution 1 for RomanDomination.six_le_weight_of_right_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T14:48:26.809427+00:00
-- url     : https://prove2.me/submissions/929bb02c-8ccb-44ee-a898-e413f363aec8

import Mathlib
import Definitions.Def_Geometry_RomanDomination_ConvexBipartite
import Definitions.Def_Geometry_RomanDomination_DoubleRoman
import Definitions.Def_Geometry_RomanDomination_Variants
open RomanDomination Finset in
theorem solution {m n : ℕ} {f : Fin m ⊕ Fin n → ℕ} (hm : 3 ≤ m) (hf : IsDRDF (K m n) f)
    (hb : ∑ j, f (Sum.inr j) ≤ 1) : 6 ≤ weight f := by
  -- every right label is at most `1`
  have hle : ∀ j, f (Sum.inr j) ≤ 1 := fun j =>
    (Finset.single_le_sum (f := fun j => f (Sum.inr j)) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ j)).trans hb
  -- so no left vertex can be labelled `0` or `1`: its neighbours are all on the right
  have hleft : ∀ i, 2 ≤ f (Sum.inl i) := by
    intro i
    by_contra hlt
    push Not at hlt
    rcases Nat.lt_succ_iff.mp hlt |>.lt_or_eq with h0 | h1
    · have h0' : f (Sum.inl i) = 0 := by omega
      rcases hf.2.1 (Sum.inl i) h0' with ⟨u, hadj, hu⟩ | ⟨u, w, -, hu, -, hu2, -⟩
      · cases u with
        | inl i' => simp at hadj
        | inr j => have := hle j; omega
      · cases u with
        | inl i' => simp at hu
        | inr j => have := hle j; omega
    · obtain ⟨u, hadj, hu⟩ := hf.2.2 (Sum.inl i) h1
      cases u with
      | inl i' => simp at hadj
      | inr j => have := hle j; omega
  have hA : 2 * m ≤ ∑ i, f (Sum.inl i) := by
    calc 2 * m = ∑ _i : Fin m, 2 := by simp [mul_comm]
      _ ≤ ∑ i, f (Sum.inl i) := Finset.sum_le_sum fun i _ => hleft i
  have hw : weight f = ∑ i, f (Sum.inl i) + ∑ j, f (Sum.inr j) := Fintype.sum_sum_type f
  omega
