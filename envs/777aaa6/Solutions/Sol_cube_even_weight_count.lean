-- Prove2me | solution 1 for cube_even_weight_count
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-05-06T22:07:25.370533+00:00
-- url     : https://prove2.me/submissions/ea485f13-0af8-4b9d-8ac7-5dbafccbc979

import Theorems.Thm_cube_even_weight_count
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Linarith

/-!
# Proof — `cube_even_weight_count`

For `d ≥ 1`, the parity-flipping involution `z ↦ flipBit z ⟨0, h_pos⟩`
bijects the even-weight class with the odd-weight class on the
Boolean `d`-cube, so the two classes have equal cardinality. Combined
with `|univ| = 2^d`, each class has cardinality `2^(d-1)`.
-/

namespace CubeParity

variable {d : ℕ}

/-- The parity-flip involution: flip the first coordinate of `z`. -/
def flipFirst (h_pos : 1 ≤ d) (z : Fin d → Bool) : Fin d → Bool :=
  Function.update z ⟨0, h_pos⟩ (! z ⟨0, h_pos⟩)

lemma flipFirst_apply_first (h_pos : 1 ≤ d) (z : Fin d → Bool) :
    flipFirst h_pos z ⟨0, h_pos⟩ = ! z ⟨0, h_pos⟩ := by
  simp [flipFirst]

lemma flipFirst_apply_other (h_pos : 1 ≤ d) (z : Fin d → Bool) {j : Fin d}
    (hj : j ≠ ⟨0, h_pos⟩) : flipFirst h_pos z j = z j := by
  simp [flipFirst, Function.update_of_ne hj]

lemma flipFirst_involutive (h_pos : 1 ≤ d) :
    Function.Involutive (flipFirst h_pos) := by
  intro z
  funext j
  by_cases hj : j = ⟨0, h_pos⟩
  · subst hj
    rw [flipFirst_apply_first, flipFirst_apply_first]
    cases z ⟨0, h_pos⟩ <;> rfl
  · rw [flipFirst_apply_other h_pos _ hj, flipFirst_apply_other h_pos _ hj]

/-- After flipping the first bit, the cardinality of the trueSet changes parity. -/
lemma flipFirst_card_parity_ne (h_pos : 1 ≤ d) (z : Fin d → Bool) :
    ((Finset.univ : Finset (Fin d)).filter (fun i => flipFirst h_pos z i)).card % 2
    ≠ ((Finset.univ : Finset (Fin d)).filter (fun i => z i)).card % 2 := by
  classical
  by_cases hz : z ⟨0, h_pos⟩ = true
  · -- flipFirst z ⟨0, h_pos⟩ = false; S' = S.erase ⟨0, h_pos⟩
    have h_eq :
        (Finset.univ : Finset (Fin d)).filter (fun i => flipFirst h_pos z i)
        = ((Finset.univ : Finset (Fin d)).filter (fun i => z i)).erase ⟨0, h_pos⟩ := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
      by_cases hj : j = ⟨0, h_pos⟩
      · subst hj
        rw [flipFirst_apply_first]
        rw [hz]
        simp
      · rw [flipFirst_apply_other h_pos _ hj]
        tauto
    have hi₀_mem :
        (⟨0, h_pos⟩ : Fin d) ∈ (Finset.univ : Finset (Fin d)).filter (fun i => z i) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hz
    rw [h_eq, Finset.card_erase_of_mem hi₀_mem]
    have hcard_pos : 0 <
        ((Finset.univ : Finset (Fin d)).filter (fun i => z i)).card :=
      Finset.card_pos.mpr ⟨_, hi₀_mem⟩
    omega
  · -- z ⟨0, h_pos⟩ = false; S' = insert ⟨0, h_pos⟩ S
    have hz' : z ⟨0, h_pos⟩ = false := by
      cases h : z ⟨0, h_pos⟩
      · rfl
      · exact absurd h hz
    have h_eq :
        (Finset.univ : Finset (Fin d)).filter (fun i => flipFirst h_pos z i)
        = insert (⟨0, h_pos⟩ : Fin d)
            ((Finset.univ : Finset (Fin d)).filter (fun i => z i)) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      by_cases hj : j = ⟨0, h_pos⟩
      · subst hj
        rw [flipFirst_apply_first, hz']
        simp
      · rw [flipFirst_apply_other h_pos _ hj]
        tauto
    have hi₀_notmem :
        (⟨0, h_pos⟩ : Fin d) ∉ (Finset.univ : Finset (Fin d)).filter (fun i => z i) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hz']
      simp
    rw [h_eq, Finset.card_insert_of_notMem hi₀_notmem]
    omega

end CubeParity

theorem solution {d : ℕ} (h_pos : 1 ≤ d) :
    ((Finset.univ : Finset (Fin d → Bool)).filter
      (fun z => ((Finset.univ : Finset (Fin d)).filter (fun i => z i)).card % 2 = 0)).card
      = 2^(d-1) := by
  classical
  set even_set : Finset (Fin d → Bool) :=
    (Finset.univ : Finset (Fin d → Bool)).filter
      (fun z => ((Finset.univ : Finset (Fin d)).filter (fun i => z i)).card % 2 = 0)
  set odd_set : Finset (Fin d → Bool) :=
    (Finset.univ : Finset (Fin d → Bool)).filter
      (fun z => ((Finset.univ : Finset (Fin d)).filter (fun i => z i)).card % 2 = 1)
  -- Step 1: |even| + |odd| = 2^d.
  have h_univ_card : (Finset.univ : Finset (Fin d → Bool)).card = 2^d := by
    rw [Finset.card_univ, Fintype.card_pi_const, Fintype.card_bool]
  have h_total : even_set.card + odd_set.card = 2^d := by
    have h_odd_eq : odd_set =
        (Finset.univ : Finset (Fin d → Bool)).filter
          (fun z => ¬ ((Finset.univ : Finset (Fin d)).filter (fun i => z i)).card % 2 = 0) := by
      apply Finset.filter_congr
      intro z _
      omega
    rw [h_odd_eq, Finset.card_filter_add_card_filter_not]
    exact h_univ_card
  -- Step 2: |even| = |odd| via flipFirst bijection.
  have h_eq : even_set.card = odd_set.card := by
    apply Finset.card_bij' (fun z _ => CubeParity.flipFirst h_pos z)
                          (fun z _ => CubeParity.flipFirst h_pos z)
    · intro z hz
      simp only [even_set, Finset.mem_filter, Finset.mem_univ, true_and] at hz
      simp only [odd_set, Finset.mem_filter, Finset.mem_univ, true_and]
      have h_par := CubeParity.flipFirst_card_parity_ne h_pos z
      omega
    · intro z hz
      simp only [odd_set, Finset.mem_filter, Finset.mem_univ, true_and] at hz
      simp only [even_set, Finset.mem_filter, Finset.mem_univ, true_and]
      have h_par := CubeParity.flipFirst_card_parity_ne h_pos z
      omega
    · intro z _
      exact CubeParity.flipFirst_involutive h_pos z
    · intro z _
      exact CubeParity.flipFirst_involutive h_pos z
  -- Step 3: combine.
  have hd_split : 2^d = 2 * 2^(d-1) := by
    obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
    rw [Nat.add_sub_cancel, pow_succ, mul_comm]
  omega
