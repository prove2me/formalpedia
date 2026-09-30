-- Prove2me | solution 1 for lean_workbook_plus_34320
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:32:43.198573+00:00
-- url     : https://prove2.me/submissions/e2d524d7-eb19-4f7d-a6a7-bccf4742350d

import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

open Filter Topology

theorem involution_shift_nonzero {f : ℝ → ℝ}
    (hInv : ∀ x > 0, f (f x) = x)
    (hShift : ∀ x > 0, f (x + 1) = f x / (f x + 1))
    {x : ℝ} (hx : 0 < x) : f x ≠ 0 := by
  intro hz
  have hs : f (x + 1) = 0 := by simp [hShift x hx, hz]
  have h₁ := hInv x hx
  have h₂ := hInv (x + 1) (by linarith)
  rw [hz] at h₁
  rw [hs] at h₂
  linarith

theorem involution_shift_inverse_step {f : ℝ → ℝ}
    (hInv : ∀ x > 0, f (f x) = x)
    (hShift : ∀ x > 0, f (x + 1) = f x / (f x + 1))
    {x : ℝ} (hx : 0 < x) : (f (x + 1))⁻¹ = (f x)⁻¹ + 1 := by
  have hz := involution_shift_nonzero hInv hShift hx
  rw [hShift x hx, inv_div]
  field_simp
  ring

theorem involution_shift_natural_values {f : ℝ → ℝ}
    (hInv : ∀ x > 0, f (f x) = x)
    (hShift : ∀ x > 0, f (x + 1) = f x / (f x + 1)) (n : ℕ) :
    f ((n : ℝ) + 1) = ((n : ℝ) + (f 1)⁻¹)⁻¹ := by
  have h (k : ℕ) : (f ((k : ℝ) + 1))⁻¹ = (k : ℝ) + (f 1)⁻¹ := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.cast_succ, involution_shift_inverse_step hInv hShift (by positivity), ih]
      ring
  simpa only [inv_inv] using congrArg Inv.inv (h n)

theorem involution_shift_natural_tendsto_zero {f : ℝ → ℝ}
    (hInv : ∀ x > 0, f (f x) = x)
    (hShift : ∀ x > 0, f (x + 1) = f x / (f x + 1)) :
    Tendsto (fun n : ℕ => f ((n : ℝ) + 1)) atTop (𝓝 0) := by
  have hTop : Tendsto (fun n : ℕ => (n : ℝ) + (f 1)⁻¹) atTop atTop :=
    tendsto_atTop_add_const_right atTop _ tendsto_natCast_atTop_atTop
  exact (tendsto_inv_atTop_zero.comp hTop).congr
    (fun n => (involution_shift_natural_values hInv hShift n).symm)

theorem no_globally_continuous_involution_shift {f : ℝ → ℝ}
    (hf : Continuous f) (hInv : ∀ x > 0, f (f x) = x)
    (hShift : ∀ x > 0, f (x + 1) = f x / (f x + 1)) : False := by
  have hlim := hf.continuousAt.tendsto.comp (involution_shift_natural_tendsto_zero hInv hShift)
  have hlim' : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop (𝓝 (f 0)) :=
    hlim.congr (fun n => hInv ((n : ℝ) + 1) (by positivity))
  exact not_tendsto_nhds_of_tendsto_atTop
    (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop) (f 0) hlim'

theorem positive_involution_fraction_step {f : ℝ → ℝ}
    (hPos : ∀ x > 0, 0 < f x) (hInv : ∀ x > 0, f (f x) = x)
    (hShift : ∀ x > 0, f (x + 1) = f x / (f x + 1))
    {x : ℝ} (hx : 0 < x) : f (x / (x + 1)) = f x + 1 := by
  have hs := hShift (f x) (hPos x hx)
  rw [hInv x hx] at hs
  have hi := hInv (f x + 1) (by have := hPos x hx; linarith)
  rwa [hs] at hi

theorem positive_involution_value_one {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Ioi 0)) (hPos : ∀ x > 0, 0 < f x)
    (hInv : ∀ x > 0, f (f x) = x)
    (hShift : ∀ x > 0, f (x + 1) = f x / (f x + 1)) : f 1 = 1 := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop
  have hq : Tendsto (fun n : ℕ => ((n : ℝ) + 1) / ((n : ℝ) + 2)) atTop (𝓝 1) := by
    have h : Tendsto (fun n : ℕ => (1 : ℝ) - ((n : ℝ) + 2)⁻¹)
        atTop (𝓝 (1 - 0)) := tendsto_const_nhds.sub (tendsto_inv_atTop_zero.comp ht)
    have he (n : ℕ) : (1 : ℝ) - ((n : ℝ) + 2)⁻¹ =
        ((n : ℝ) + 1) / ((n : ℝ) + 2) := by
      have hn : (n : ℝ) + 2 ≠ 0 := by positivity
      field_simp
      ring
    simpa only [sub_zero] using h.congr he
  have hc : ContinuousAt f 1 := hf.continuousAt (Ioi_mem_nhds zero_lt_one)
  have hleft := hc.tendsto.comp hq
  have hright : Tendsto (fun n : ℕ => f (((n : ℝ) + 1) / ((n : ℝ) + 2)))
      atTop (𝓝 1) := by
    have h := (involution_shift_natural_tendsto_zero hInv hShift).add_const 1
    apply (show Tendsto (fun n : ℕ => f ((n : ℝ) + 1) + 1) atTop (𝓝 1) by
      simpa only [zero_add] using h).congr
    intro n
    have h := positive_involution_fraction_step hPos hInv hShift
      (x := (n : ℝ) + 1) (by positivity)
    convert h.symm using 1
    congr 2
    ring
  exact tendsto_nhds_unique hleft hright

theorem positive_involution_natural_ratios {f : ℝ → ℝ}
    (hPos : ∀ x > 0, 0 < f x) (hInv : ∀ x > 0, f (f x) = x)
    (hShift : ∀ x > 0, f (x + 1) = f x / (f x + 1)) (hOne : f 1 = 1)
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) : f ((m : ℝ) / n) = (n : ℝ) / m := by
  have H : ∀ k m n : ℕ, m + n = k → 0 < m → 0 < n →
      f ((m : ℝ) / n) = (n : ℝ) / m := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro m n hsum hm hn
      have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
      have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
      rcases lt_trichotomy m n with hmn | he | hnm
      · have hd : 0 < n - m := Nat.sub_pos_of_lt hmn
        have hdR : (0 : ℝ) < (n - m : ℕ) := Nat.cast_pos.mpr hd
        have hc : ((n - m : ℕ) : ℝ) = (n : ℝ) - m := Nat.cast_sub hmn.le
        have hr := ih n (by omega) m (n - m) (by omega) hm hd
        have ha : (m : ℝ) / n = ((m : ℝ) / (n - m : ℕ)) /
            ((m : ℝ) / (n - m : ℕ) + 1) := by
          have hs : (m : ℝ) / (n - m : ℕ) + 1 ≠ 0 := by positivity
          field_simp
          rw [hc]
          ring
        calc
          f ((m : ℝ) / n) = f (((m : ℝ) / (n - m : ℕ)) /
              ((m : ℝ) / (n - m : ℕ) + 1)) := congrArg f ha
          _ = f ((m : ℝ) / (n - m : ℕ)) + 1 :=
            positive_involution_fraction_step hPos hInv hShift (by positivity)
          _ = (n : ℝ) / m := by rw [hr, hc]; field_simp; ring
      · subst n
        simpa only [div_self hmR.ne'] using hOne
      · have hd : 0 < m - n := Nat.sub_pos_of_lt hnm
        have hdR : (0 : ℝ) < (m - n : ℕ) := Nat.cast_pos.mpr hd
        have hc : ((m - n : ℕ) : ℝ) = (m : ℝ) - n := Nat.cast_sub hnm.le
        have hr := ih m (by omega) (m - n) n (by omega) hd hn
        have ha : (m : ℝ) / n = ((m - n : ℕ) : ℝ) / n + 1 := by
          rw [hc]
          field_simp
          ring
        calc
          f ((m : ℝ) / n) = f (((m - n : ℕ) : ℝ) / n + 1) := congrArg f ha
          _ = f (((m - n : ℕ) : ℝ) / n) /
              (f (((m - n : ℕ) : ℝ) / n) + 1) := hShift _ (by positivity)
          _ = (n : ℝ) / m := by
            rw [hr]
            have hs : (n : ℝ) / (m - n : ℕ) + 1 ≠ 0 := by positivity
            field_simp
            rw [hc]
            ring
  exact H (m + n) m n rfl hm hn

theorem positive_involution_rational_values {f : ℝ → ℝ}
    (hPos : ∀ x > 0, 0 < f x) (hInv : ∀ x > 0, f (f x) = x)
    (hShift : ∀ x > 0, f (x + 1) = f x / (f x + 1)) (hOne : f 1 = 1)
    (q : ℚ) (hq : 0 < (q : ℝ)) : f (q : ℝ) = (q : ℝ)⁻¹ := by
  have hq' : 0 < q := by exact_mod_cast hq
  have hn : 0 < q.num := Rat.num_pos.mpr hq'
  have ha : (q.num.natAbs : ℤ) = q.num := Int.natAbs_of_nonneg hn.le
  have hm : 0 < q.num.natAbs := by omega
  have he : (q : ℝ) = (q.num.natAbs : ℝ) / q.den := by
    rw [Rat.cast_def]
    congr 1
    simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z : ℝ)) ha.symm
  rw [he, positive_involution_natural_ratios hPos hInv hShift hOne _ _ hm q.pos,
    inv_div]

theorem positive_involution_full_classification {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Ioi 0)) (hPos : ∀ x > 0, 0 < f x)
    (hInv : ∀ x > 0, f (f x) = x)
    (hShift : ∀ x > 0, f (x + 1) = f x / (f x + 1)) :
    ∀ x > 0, f x = 1 / x := by
  have hOne := positive_involution_value_one hf hPos hInv hShift
  have hEq : Set.EqOn f (fun x : ℝ => x⁻¹)
      (Set.Ioi 0 ∩ Set.range ((↑) : ℚ → ℝ)) := by
    rintro x ⟨hx, q, rfl⟩
    exact positive_involution_rational_values hPos hInv hShift hOne q hx
  have hCont : ContinuousOn (fun x : ℝ => x⁻¹) (Set.Ioi 0) :=
    continuousOn_id.inv₀ (fun x hx => ne_of_gt hx)
  have hDense : Set.Ioi (0 : ℝ) ⊆ closure (Set.Ioi 0 ∩ Set.range ((↑) : ℚ → ℝ)) := by
    intro x hx
    exact isOpen_Ioi.inter_closure ⟨hx, Rat.denseRange_cast x⟩
  have hFull := hEq.of_subset_closure hf hCont (fun _ hx => hx.1) hDense
  intro x hx
  simpa only [one_div] using hFull hx

theorem positive_involution_classification_iff (f : ℝ → ℝ) :
    (ContinuousOn f (Set.Ioi 0) ∧ (∀ x > 0, 0 < f x) ∧
      (∀ x > 0, f (f x) = x) ∧
      (∀ x > 0, f (x + 1) = f x / (f x + 1))) ↔
      ∀ x > 0, f x = 1 / x := by
  constructor
  · rintro ⟨hf, hPos, hInv, hShift⟩
    exact positive_involution_full_classification hf hPos hInv hShift
  · intro hEq
    have hPos : ∀ x > 0, 0 < f x := by
      intro x hx
      rw [hEq x hx]
      positivity
    refine ⟨?_, hPos, ?_, ?_⟩
    · exact (continuousOn_id.inv₀ (fun x (hx : x ∈ Set.Ioi (0 : ℝ)) =>
        ne_of_gt hx)).congr (fun x hx => by simpa only [one_div] using hEq x hx)
    · intro x hx
      rw [hEq (f x) (hPos x hx), hEq x hx]
      simp
    · intro x hx
      rw [hEq (x + 1) (by linarith), hEq x hx]
      have hx0 := hx.ne'
      have hx1 : x + 1 ≠ 0 := by linarith
      field_simp
      ring

theorem solution (f : ℝ → ℝ) (hf : Continuous f)
    (hf1 : ∀ x > 0, f (f x) = x)
    (hf2 : ∀ x > 0, f (x + 1) = f x / (f x + 1)) :
    ∀ x > 0, f x = 1 / (x + 1) := by
  exact False.elim (no_globally_continuous_involution_shift hf hf1 hf2)

#print axioms involution_shift_nonzero
#print axioms involution_shift_inverse_step
#print axioms involution_shift_natural_values
#print axioms involution_shift_natural_tendsto_zero
#print axioms no_globally_continuous_involution_shift
#print axioms positive_involution_fraction_step
#print axioms positive_involution_value_one
#print axioms positive_involution_natural_ratios
#print axioms positive_involution_rational_values
#print axioms positive_involution_full_classification
#print axioms positive_involution_classification_iff
#print axioms solution
