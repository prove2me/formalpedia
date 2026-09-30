-- Prove2me | solution 1 for lean_workbook_plus_19946
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T09:08:59.170463+00:00
-- url     : https://prove2.me/submissions/0feb1b7a-93ce-468b-87ff-f51563b067cd

import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Order.Iterate
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

open Set Function

theorem positive_iterate_identity_injOn {α : Type*} (f : α → α) (s : Set α)
    (n : ℕ) (hn : 0 < n) (hi : ∀ x ∈ s, f^[n] x = x) : InjOn f s := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  intro x hx y hy hxy
  calc
    x = f^[k + 1] x := (hi x hx).symm
    _ = f^[k] (f x) := iterate_succ_apply f k x
    _ = f^[k] (f y) := congrArg (f^[k]) hxy
    _ = f^[k + 1] y := (iterate_succ_apply f k y).symm
    _ = y := hi y hy

theorem strictMonoOn_periodic_point_fixed {α : Type*} [LinearOrder α]
    (f : α → α) (s : Set α) (hm : MapsTo f s s) (hf : StrictMonoOn f s)
    (n : ℕ) (hn : 0 < n) (x : α) (hx : x ∈ s) (hi : f^[n] x = x) : f x = x := by
  let F : s → s := hm.restrict f s s
  have hF : StrictMono F := fun u v huv => hf u.property v.property huv
  have hc : Function.Commute F id := fun _ => rfl
  have hiter : F^[n] ⟨x, hx⟩ = ⟨x, hx⟩ := by
    apply Subtype.ext
    change ((hm.restrict f s s)^[n] ⟨x, hx⟩).val = x
    rw [hm.iterate_restrict]
    exact hi
  have hfixed : F ⟨x, hx⟩ = ⟨x, hx⟩ := by
    apply (hc.iterate_pos_eq_iff_map_eq hF.monotone strictMono_id hn).mp
    simpa only [iterate_id, id_eq] using hiter
  exact congrArg Subtype.val hfixed

theorem continuous_finite_order_Icc_strictMono (f : ℝ → ℝ) (a b : ℝ)
    (hab : a ≤ b) (hc : ContinuousOn f (Icc a b)) (ha : f a = a) (hb : f b = b)
    (n : ℕ) (hn : 0 < n) (hi : ∀ x ∈ Icc a b, f^[n] x = x) :
    StrictMonoOn f (Icc a b) := by
  apply hc.strictMonoOn_of_injOn_Icc hab
  · simpa only [ha, hb] using hab
  · exact positive_iterate_identity_injOn f (Icc a b) n hn hi

theorem continuous_finite_order_Icc_mapsTo (f : ℝ → ℝ) (a b : ℝ)
    (hab : a ≤ b) (hc : ContinuousOn f (Icc a b)) (ha : f a = a) (hb : f b = b)
    (n : ℕ) (hn : 0 < n) (hi : ∀ x ∈ Icc a b, f^[n] x = x) :
    MapsTo f (Icc a b) (Icc a b) := by
  have hm := (continuous_finite_order_Icc_strictMono f a b hab hc ha hb n hn hi).monotoneOn
  intro x hx
  constructor
  · simpa only [ha] using hm (left_mem_Icc.mpr hab) hx hx.1
  · simpa only [hb] using hm hx (right_mem_Icc.mpr hab) hx.2

theorem continuous_finite_order_Icc_identity (f : ℝ → ℝ) (a b : ℝ)
    (hab : a ≤ b) (hc : ContinuousOn f (Icc a b)) (ha : f a = a) (hb : f b = b)
    (n : ℕ) (hn : 0 < n) (hi : ∀ x ∈ Icc a b, f^[n] x = x) :
    ∀ x ∈ Icc a b, f x = x := by
  have hm := continuous_finite_order_Icc_mapsTo f a b hab hc ha hb n hn hi
  have hs := continuous_finite_order_Icc_strictMono f a b hab hc ha hb n hn hi
  exact fun x hx => strictMonoOn_periodic_point_fixed f (Icc a b) hm hs n hn x hx (hi x hx)

theorem continuous_finite_order_Icc_iff (f : ℝ → ℝ) (a b : ℝ)
    (hab : a ≤ b) (hc : ContinuousOn f (Icc a b)) (ha : f a = a) (hb : f b = b)
    (n : ℕ) (hn : 0 < n) :
    (∀ x ∈ Icc a b, f^[n] x = x) ↔ ∀ x ∈ Icc a b, f x = x := by
  constructor
  · exact continuous_finite_order_Icc_identity f a b hab hc ha hb n hn
  · exact fun hi x hx => iterate_fixed (hi x hx) n

theorem continuous_finite_order_interval_classification (f : ℝ → ℝ) (hc : Continuous f) :
    (f 0 = 0 ∧ f 1 = 1 ∧ ∃ n : ℕ, 0 < n ∧ ∀ x ∈ Icc (0 : ℝ) 1, f^[n] x = x) ↔
      ∀ x ∈ Icc (0 : ℝ) 1, f x = x := by
  constructor
  · rintro ⟨h0, h1, n, hn, hi⟩
    exact continuous_finite_order_Icc_identity f 0 1 (by norm_num) hc.continuousOn h0 h1 n hn hi
  · intro hi
    exact ⟨hi 0 (by norm_num), hi 1 (by norm_num), 1, by omega,
      fun x hx => iterate_fixed (hi x hx) 1⟩

theorem continuous_all_iterates_interval_classification (f : ℝ → ℝ) (hc : Continuous f) :
    (f 0 = 0 ∧ f 1 = 1 ∧ ∀ n : ℕ, 0 < n → ∀ x ∈ Icc (0 : ℝ) 1, f^[n] x = x) ↔
      ∀ x ∈ Icc (0 : ℝ) 1, f x = x := by
  constructor
  · rintro ⟨h0, h1, hi⟩
    exact continuous_finite_order_Icc_identity f 0 1 (by norm_num) hc.continuousOn
      h0 h1 1 (by omega) (hi 1 (by omega))
  · intro hi
    exact ⟨hi 0 (by norm_num), hi 1 (by norm_num), fun n _ x hx => iterate_fixed (hi x hx) n⟩

theorem solution (x : ℝ) (n : ℕ) (f : ℝ → ℝ)
    (hf : f x = 0 ∧ f 1 = 1 ∧ ∀ x ∈ Set.Icc (0 : ℝ) 1, f^[n] x = x) :
    ∃ f : ℝ → ℝ, f x = 0 ∧ f 1 = 1 ∧ ∀ x ∈ Set.Icc (0 : ℝ) 1, f^[n] x = x := by
  exact ⟨f, hf⟩

#print axioms positive_iterate_identity_injOn
#print axioms strictMonoOn_periodic_point_fixed
#print axioms continuous_finite_order_Icc_strictMono
#print axioms continuous_finite_order_Icc_mapsTo
#print axioms continuous_finite_order_Icc_identity
#print axioms continuous_finite_order_Icc_iff
#print axioms continuous_finite_order_interval_classification
#print axioms continuous_all_iterates_interval_classification
#print axioms solution
