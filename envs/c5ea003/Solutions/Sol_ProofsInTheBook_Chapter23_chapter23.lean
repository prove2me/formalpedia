-- Prove2me | solution 1 for ProofsInTheBook.Chapter23.chapter23
-- status  : ACCEPTED   (prove)
-- author  : @Xiang Huang
-- created : 2026-09-12T16:13:00.962916+00:00
-- url     : https://prove2.me/submissions/ce88e301-f56c-4685-8c94-165530ace68c

import Mathlib
import Definitions.Def_ProofsInTheBook_Chapter23


/-!
# Chapter 23: On a lemma of Littlewood and Offord

From "Proofs from THE BOOK":

**Littlewood-Offord lemma**: Among all 2ⁿ sums ±a₁ ± a₂ ± ⋯ ± aₙ
(with |aᵢ| ≥ 1), at most C(n, ⌊n/2⌋) lie in any interval of length 2.

The book presents Erdős's elegant proof using Dilworth's theorem
(or the LYM inequality) to bound antichains in the power set.
-/

namespace ProofsInTheBook.Chapter23

open Finset

noncomputable section

/-!
### Erdős's reduction to Sperner

We formalize the standard subset-sum form used in the Littlewood-Offord proof.
If every weight is at least `1`, then two comparable subsets have sums differing
by at least `1`. Hence all subsets whose sums lie in the same half-open interval
`[x, x + 1)` form an antichain, and Sperner's theorem gives the middle-layer
bound.
-/





theorem chapter23_sperner_via_lym {α : Type*} [Fintype α] [DecidableEq α]
    (𝒜 : Finset (Finset α))
    (h𝒜 : IsAntichain (· ⊆ ·) (𝒜 : Set (Finset α))) :
    𝒜.card ≤ (Fintype.card α).choose (Fintype.card α / 2) := by
  have hmiddle_pos : 0 < ((Fintype.card α).choose (Fintype.card α / 2) : ℚ≥0) :=
    Nat.cast_pos.2 <| Nat.choose_pos (Nat.div_le_self _ _)
  have hlym := calc
    ∑ s ∈ 𝒜, ((Fintype.card α).choose (Fintype.card α / 2) : ℚ≥0)⁻¹
      ≤ ∑ s ∈ 𝒜, ((Fintype.card α).choose #s : ℚ≥0)⁻¹ := by
        gcongr with s hs
        · exact mod_cast Nat.choose_pos s.card_le_univ
        · exact Nat.choose_le_middle _ _
    _ ≤ 1 := Finset.lubell_yamamoto_meshalkin_inequality_sum_inv_choose h𝒜
  simpa [mul_inv_le_iff₀' hmiddle_pos] using hlym

theorem subsetSum_mono {n : ℕ} {a : Fin n → ℝ}
    (ha : ∀ i, 1 ≤ a i) {s t : Finset (Fin n)} (hst : s ⊆ t) :
    subsetSum a s ≤ subsetSum a t := by
  unfold subsetSum
  exact Finset.sum_le_sum_of_subset_of_nonneg hst fun i _ _ => (zero_le_one.trans (ha i))

theorem subsetSum_antichain {n : ℕ} {a : Fin n → ℝ} (ha : ∀ i, 1 ≤ a i) (x : ℝ) :
    IsAntichain (· ⊆ ·) (shortIntervalSubsetSums a x : Set (Finset (Fin n))) := by
  intro s hs t ht hne hst
  have hs_interval : x ≤ subsetSum a s ∧ subsetSum a s < x + 1 :=
    (Finset.mem_filter.mp hs).2
  have ht_interval : x ≤ subsetSum a t ∧ subsetSum a t < x + 1 :=
    (Finset.mem_filter.mp ht).2
  have hproper : s ⊂ t := Finset.ssubset_iff_subset_ne.2 ⟨hst, hne⟩
  obtain ⟨i, hit, his⟩ := Finset.exists_of_ssubset hproper
  have hinsert : insert i s ⊆ t := by
    intro j hj
    rw [Finset.mem_insert] at hj
    rcases hj with rfl | hjs
    · exact hit
    · exact hst hjs
  have hmono : subsetSum a (insert i s) ≤ subsetSum a t :=
    subsetSum_mono ha hinsert
  have hinsert_sum : subsetSum a (insert i s) = a i + subsetSum a s := by
    simp [subsetSum, his]
  have hstep : subsetSum a s + 1 ≤ subsetSum a t := by
    have hfirst : subsetSum a s + 1 ≤ subsetSum a (insert i s) := by
      rw [hinsert_sum]
      linarith [ha i]
    exact hfirst.trans hmono
  have : x + 1 < x + 1 := by
    calc
      x + 1 ≤ subsetSum a s + 1 := by
        simpa [add_comm, add_left_comm, add_assoc] using add_le_add_right hs_interval.1 1
      _ ≤ subsetSum a t := hstep
      _ < x + 1 := ht_interval.2
  exact (lt_irrefl (x + 1)) this

theorem chapter23_littlewood_offord_subset_sums {n : ℕ} (a : Fin n → ℝ)
    (ha : ∀ i, 1 ≤ a i) (x : ℝ) :
    (shortIntervalSubsetSums a x).card ≤ n.choose (n / 2) := by
  simpa using
    (chapter23_sperner_via_lym (shortIntervalSubsetSums a x) (subsetSum_antichain ha x))



end

end ProofsInTheBook.Chapter23

open Finset
open ProofsInTheBook.Chapter23

theorem solution {n : ℕ} (a : Fin n → ℝ) (ha : ∀ i, 1 ≤ a i) (x : ℝ) :
    (shortIntervalSubsetSums a x).card ≤ n.choose (n / 2) :=
  chapter23_littlewood_offord_subset_sums a ha x
