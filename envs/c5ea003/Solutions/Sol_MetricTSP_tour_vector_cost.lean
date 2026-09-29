-- Prove2me | solution 1 for MetricTSP.tour_vector_cost
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-24T19:22:39.895116+00:00
-- url     : https://prove2.me/submissions/3363cc95-d3a2-4de5-ba54-aa668555028b

import Mathlib
import Definitions.Def_MetricTSP_model
import Definitions.Def_MetricTSP_tour_vector

namespace MetricTSP

open Finset

variable {n : ℕ}

lemma rot_val (i : Fin n) : (finRotate n i).val = (i.val + 1) % n := by
  have : NeZero n := ⟨Nat.pos_iff_ne_zero.mp i.pos⟩
  rw [finRotate_apply, Fin.add_def, Fin.val_one']
  conv_rhs => rw [Nat.add_mod, Nat.mod_eq_of_lt i.isLt]

lemma rot_ne (hn : 2 ≤ n) (i : Fin n) : finRotate n i ≠ i := by
  intro h
  have hv := congrArg Fin.val h
  rw [rot_val] at hv
  have hlt := i.isLt
  rcases Nat.lt_or_ge (i.val + 1) n with h1 | h1
  · rw [Nat.mod_eq_of_lt h1] at hv; omega
  · have he : i.val + 1 = n := by omega
    rw [he, Nat.mod_self] at hv
    omega

lemma rot_rot_ne (hn : 3 ≤ n) (i : Fin n) : finRotate n (finRotate n i) ≠ i := by
  intro h
  have hv := congrArg Fin.val h
  rw [rot_val, rot_val] at hv
  have hlt := i.isLt
  rcases Nat.lt_or_ge (i.val + 1) n with h1 | h1
  · rw [Nat.mod_eq_of_lt h1] at hv
    rcases Nat.lt_or_ge (i.val + 1 + 1) n with h2 | h2
    · rw [Nat.mod_eq_of_lt h2] at hv; omega
    · have he : i.val + 1 + 1 = n := by omega
      rw [he, Nat.mod_self] at hv; omega
  · have he : i.val + 1 = n := by omega
    rw [he, Nat.mod_self] at hv
    have h01 : (0 + 1) % n = 1 := Nat.mod_eq_of_lt (by omega)
    rw [h01] at hv
    omega

/-- The incidence vector as a sum of step indicators. -/
lemma tourVec_eq_sum (hn : 2 ≤ n) (π : Equiv.Perm (Fin n)) (u v : Fin n) :
    tourVec π u v = ∑ i : Fin n,
      ((if π i = u ∧ π (finRotate n i) = v then (1 : ℝ) else 0)
        + (if π i = v ∧ π (finRotate n i) = u then (1 : ℝ) else 0)) := by
  unfold tourVec tourSteps
  rw [Finset.card_filter, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hnab : ¬((π i = u ∧ π (finRotate n i) = v) ∧ (π i = v ∧ π (finRotate n i) = u)) := by
    rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
    have huv : u = v := h1.symm.trans h3
    exact rot_ne hn i (π.injective (h2.trans (huv ▸ h1.symm)))
  rcases Classical.em (π i = u ∧ π (finRotate n i) = v) with hA | hA <;>
    rcases Classical.em (π i = v ∧ π (finRotate n i) = u) with hB | hB
  · exact absurd ⟨hA, hB⟩ hnab
  · rw [if_pos (Or.inl hA), if_pos hA, if_neg hB]; norm_num
  · rw [if_pos (Or.inr hB), if_neg hA, if_pos hB]; norm_num
  · have hor : ¬((π i = u ∧ π (finRotate n i) = v) ∨ (π i = v ∧ π (finRotate n i) = u)) := by
      rintro (h | h)
      exacts [hA h, hB h]
    rw [if_neg hor, if_neg hA, if_neg hB]; norm_num

lemma sum_comm3 (F : Fin n → Fin n → Fin n → ℝ) :
    ∑ u : Fin n, ∑ v : Fin n, ∑ i : Fin n, F u v i
      = ∑ i : Fin n, ∑ u : Fin n, ∑ v : Fin n, F u v i :=
  calc ∑ u : Fin n, ∑ v : Fin n, ∑ i : Fin n, F u v i
      = ∑ u : Fin n, ∑ i : Fin n, ∑ v : Fin n, F u v i :=
        Finset.sum_congr rfl fun u _ => Finset.sum_comm
    _ = ∑ i : Fin n, ∑ u : Fin n, ∑ v : Fin n, F u v i := Finset.sum_comm

/-- The LP objective of the tour vector is exactly twice the tour cost. -/
lemma tourVec_objective (hn : 3 ≤ n) (c : Fin n → Fin n → ℝ)
    (hsym : ∀ u v, c u v = c v u) (π : Equiv.Perm (Fin n)) :
    ∑ u, ∑ v, c u v * tourVec π u v = 2 * tourCost c π := by
  have h2 : 2 ≤ n := by omega
  calc ∑ u, ∑ v, c u v * tourVec π u v
      = ∑ u, ∑ v, ∑ i : Fin n,
          ((if π i = u ∧ π (finRotate n i) = v then c u v else 0)
            + (if π i = v ∧ π (finRotate n i) = u then c u v else 0)) := by
        apply Finset.sum_congr rfl; intro u _
        apply Finset.sum_congr rfl; intro v _
        rw [tourVec_eq_sum h2, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro i _
        rw [mul_add, mul_ite, mul_one, mul_zero, mul_ite, mul_one, mul_zero]
    _ = ∑ i : Fin n, ∑ u, ∑ v,
          ((if π i = u ∧ π (finRotate n i) = v then c u v else 0)
            + (if π i = v ∧ π (finRotate n i) = u then c u v else 0)) :=
        sum_comm3 (fun u v i =>
          ((if π i = u ∧ π (finRotate n i) = v then c u v else 0)
            + (if π i = v ∧ π (finRotate n i) = u then c u v else 0)))
    _ = ∑ i : Fin n,
          (c (π i) (π (finRotate n i)) + c (π (finRotate n i)) (π i)) := by
        apply Finset.sum_congr rfl; intro i _
        have e1 : ∑ u : Fin n, ∑ v : Fin n,
              ((if π i = u ∧ π (finRotate n i) = v then c u v else 0)
                + (if π i = v ∧ π (finRotate n i) = u then c u v else 0))
            = (∑ u : Fin n, ∑ v : Fin n,
                (if π i = u ∧ π (finRotate n i) = v then c u v else 0))
              + (∑ u : Fin n, ∑ v : Fin n,
                (if π i = v ∧ π (finRotate n i) = u then c u v else 0)) := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun u _ => Finset.sum_add_distrib
        rw [e1]
        congr 1
        · have hu : ∀ u : Fin n, ∑ v, (if π i = u ∧ π (finRotate n i) = v then c u v else 0)
              = if π i = u then c u (π (finRotate n i)) else 0 := by
            intro u
            by_cases h : π i = u <;> simp [h]
          rw [Finset.sum_congr rfl fun u _ => hu u]
          simp
        · have hu : ∀ u : Fin n, ∑ v, (if π i = v ∧ π (finRotate n i) = u then c u v else 0)
              = if π (finRotate n i) = u then c u (π i) else 0 := by
            intro u
            rcases Classical.em (π (finRotate n i) = u) with h | h
            · rw [if_pos h,
                Finset.sum_congr rfl fun v _ => if_congr (and_iff_left h) rfl rfl]
              simp
            · rw [if_neg h,
                Finset.sum_congr rfl fun v _ => if_neg (fun hc => h hc.2)]
              simp
          rw [Finset.sum_congr rfl fun u _ => hu u]
          simp
    _ = ∑ i : Fin n, 2 * c (π i) (π (finRotate n i)) := by
        apply Finset.sum_congr rfl; intro i _
        rw [hsym (π (finRotate n i)) (π i)]
        ring
    _ = 2 * tourCost c π := by
        rw [tourCost, Finset.mul_sum]


end MetricTSP

open MetricTSP

theorem solution (n : ℕ) (hn : 3 ≤ n) (c : Fin n → Fin n → ℝ)
    (hsym : ∀ u v, c u v = c v u) (π : Equiv.Perm (Fin n)) :
    ∑ u, ∑ v, c u v * tourVec π u v = 2 * tourCost c π :=
  MetricTSP.tourVec_objective hn c hsym π
