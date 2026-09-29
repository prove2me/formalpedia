-- Prove2me | solution 1 for mme_released_recursive_data_structure_valid
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-22T17:37:11.010995+00:00
-- url     : https://prove2.me/submissions/35183413-9d43-47d7-8418-154b04b0d65b

import Mathlib
import Definitions.Def_mme_released_recursive_level_data
import Definitions.Def_mme_recursive_yz_owned_filters
open BigOperators MME MME.RecursiveYZ MME.ReleasedRecursive MME.MoreAsymmetryExactSeed
set_option autoImplicit false
set_option maxHeartbeats 4000000

open BigOperators MME MME.RecursiveYZ MME.ReleasedRecursive MME.MoreAsymmetryExactSeed
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace MME.ReleasedRecursive

theorem childP_sum_pairs' (x y s0 k : ℕ) (hs : x + y ≤ 4) (hk : k < 3) (h0 : 2 * s0 ≤ denominator) :
    ∑ a : Fin 3, ∑ b : Fin 3, childP [x, y, 4 - x - y] s0 k a.val b.val = denominator := by
  have hx : x ≤ 4 := by omega
  have hy : y ≤ 4 := by omega
  interval_cases x <;> interval_cases y <;> interval_cases k <;>
    simp [childP, jointWeight, elementary, listSub, Fin.sum_univ_three, denominator] at h0 hs ⊢ <;> omega

theorem childP_sum_pairs (x y z s0 k : ℕ) (hs : x + y + z = 4) (hk : k < 3) (h0 : 2 * s0 ≤ denominator) :
    ∑ a : Fin 3, ∑ b : Fin 3, childP [x, y, z] s0 k a.val b.val = denominator := by
  obtain rfl : z = 4 - x - y := by omega
  exact childP_sum_pairs' x y s0 k (by omega) hk h0

end MME.ReleasedRecursive

open BigOperators MME MME.RecursiveYZ MME.ReleasedRecursive MME.MoreAsymmetryExactSeed
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace MME.ReleasedRecursive

/-! Seed-level facts, decided by the kernel on small numbers. -/

theorem hs0_all : ∀ j : Fin 126,
    ((seedTerm (posTerm j).1 (posTerm j).2).children.all fun x ↦ decide (2 * x.2.2 ≤ denominator)) = true := by
  decide +kernel

theorem term3_lt : ∀ ρ : Fin 6, ∀ r : Fin 88, term3 ρ r < 126 := by decide +kernel

theorem termS0_le (j : ℕ) (hj : j < 126) (ρ : ℕ) (c : List ℕ) : 2 * termS0 j ρ c ≤ denominator := by
  unfold termS0
  split
  · rename_i x hx
    have hmem := List.mem_of_find?_eq_some hx
    have hall := hs0_all ⟨j, hj⟩
    rw [List.all_eq_true] at hall
    simpa using hall x hmem
  · simp

theorem physOf_sum (ρ : Fin 6) (v : Fin 3 → ℕ) :
    (physOf ρ v).getD 0 0 + (physOf ρ v).getD 1 0 + (physOf ρ v).getD 2 0 = v 0 + v 1 + v 2 := by
  fin_cases ρ <;> simp [physOf, invRoles] <;> omega

theorem physOf_eq (ρ : Fin 6) (v : Fin 3 → ℕ) :
    physOf ρ v = [(physOf ρ v).getD 0 0, (physOf ρ v).getD 1 0, (physOf ρ v).getD 2 0] := by
  simp [physOf]

theorem roles_lt (ρ : Fin 6) (i : Fin 3) : (ReleasedGlobal.roles ρ i).val < 3 := (ReleasedGlobal.roles ρ i).isLt

/-- Sum over complete level-2 words as a double sum over the two letters. -/
theorem sum_word2 (f : ℕ → ℕ → ℕ) :
    ∑ w : CompleteSplit.CompleteWord 2, f (w 0).val (w 1).val = ∑ a : Fin 3, ∑ b : Fin 3, f a.val b.val := by
  rw [← Fintype.sum_prod_type']
  exact Fintype.sum_equiv (finTwoArrowEquiv (Fin 3)) _ _ (fun _ ↦ rfl)

theorem m3_dvd (ρ : Fin 6) (r : Fin 88) (c) : denominator ∣ m3 ρ r c := by
  unfold m3
  exact Dvd.dvd.mul_left (dvd_pow_self _ (by norm_num)) _

theorem hmass3 (ρ : Fin 6) (i : Fin 3) (c : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 ρ)) :
    ∑ w, mu3 ρ i c w = m3 ρ c.1 c.2 + m3 ρ c.1 (complement (htotal3 ρ c.1) c.2) := by
  set M := m3 ρ c.1 c.2 + m3 ρ c.1 (complement (htotal3 ρ c.1) c.2) with hM
  have hD : denominator ∣ M := dvd_add (m3_dvd _ _ _) (m3_dvd _ _ _)
  obtain ⟨M', hM'⟩ := hD
  set v : Fin 3 → ℕ := fun i ↦ (c.2.val i).val with hv
  have hsum : v 0 + v 1 + v 2 = 4 := c.2.property.1
  have hs := physOf_sum ρ v
  have hpos : 0 < denominator := by norm_num [denominator]
  have key := childP_sum_pairs ((physOf ρ v).getD 0 0) ((physOf ρ v).getD 1 0) ((physOf ρ v).getD 2 0)
    (termS0 (term3 ρ c.1) ρ (physOf ρ v)) (ReleasedGlobal.roles ρ i).val (by omega) (roles_lt ρ i)
    (termS0_le _ (term3_lt ρ c.1) _ _)
  rw [← physOf_eq] at key
  unfold mu3
  rw [← hM, hM']
  have hterm : ∀ w : CompleteSplit.CompleteWord 2,
      denominator * M' * childP (physOf ρ v) (termS0 (term3 ρ c.1) ρ (physOf ρ v))
        (ReleasedGlobal.roles ρ i) (w 0).val (w 1).val / denominator =
      M' * childP (physOf ρ v) (termS0 (term3 ρ c.1) ρ (physOf ρ v))
        (ReleasedGlobal.roles ρ i) (w 0).val (w 1).val := by
    intro w
    rw [mul_assoc, Nat.mul_div_cancel_left _ hpos]
  simp only [hv] at hterm key ⊢
  rw [Finset.sum_congr rfl (fun w _ ↦ hterm w), ← Finset.mul_sum,
    sum_word2 (fun a b ↦ childP _ _ _ a b), key, mul_comm]


/-- Level-3 counts: split masses sum to the parent count, and every count is positive. -/
theorem n3_eq (ρ : Fin 6) (r : Fin 88) :
    n3 ρ r = termGalpha (term3 ρ r) * termRegion (term3 ρ r) ρ * denominator ^ 3 := rfl

theorem hm3_of_alpha (ρ : Fin 6) (r : Fin 88)
    (h : ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (2 - 1)) (parent3 ρ r),
      termAlpha (term3 ρ r) ρ (physOf ρ fun i ↦ (c.val i).val) = denominator) :
    ∑ c, m3 ρ r c = n3 ρ r := by
  unfold m3
  rw [show (fun c : RecursiveThinSplit.Split (2 * 2 ^ (2 - 1)) (parent3 ρ r) ↦
      termGalpha (term3 ρ r) * termRegion (term3 ρ r) ρ *
        termAlpha (term3 ρ r) ρ (physOf ρ fun i ↦ (c.val i).val) * denominator ^ 2) =
    (fun c ↦ (termGalpha (term3 ρ r) * termRegion (term3 ρ r) ρ * denominator ^ 2) *
        termAlpha (term3 ρ r) ρ (physOf ρ fun i ↦ (c.val i).val)) from funext fun c ↦ by ring,
    ← Finset.mul_sum, h, n3_eq]
  ring

theorem hn3_of_pos (ρ : Fin 6) (r : Fin 88)
    (h : 0 < termGalpha (term3 ρ r) ∧ 0 < termRegion (term3 ρ r) ρ) : 0 < n3 ρ r := by
  rw [n3_eq]
  exact Nat.mul_pos (Nat.mul_pos h.1 h.2) (by norm_num [denominator])

theorem n2_dvd (r : Fin 1104) : denominator ∣ n2 r :=
  Dvd.dvd.mul_left (dvd_pow_self _ (by norm_num)) _

theorem hm2_of_weights (r : Fin 1104)
    (h : ∑ e : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 r),
      jointWeight (level2At r).2.2 (termS0 (level2At r).1 (level2At r).2.1 (level2At r).2.2)
        [(e.val 0).val, (e.val 1).val, (e.val 2).val] = denominator) :
    ∑ e, m2 r e = n2 r := by
  obtain ⟨N, hN⟩ := n2_dvd r
  have hpos : 0 < denominator := by norm_num [denominator]
  unfold m2
  have hterm : ∀ e : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 r),
      n2 r * jointWeight (level2At r).2.2 (termS0 (level2At r).1 (level2At r).2.1 (level2At r).2.2)
        [(e.val 0).val, (e.val 1).val, (e.val 2).val] / denominator =
      N * jointWeight (level2At r).2.2 (termS0 (level2At r).1 (level2At r).2.1 (level2At r).2.2)
        [(e.val 0).val, (e.val 1).val, (e.val 2).val] := by
    intro e
    rw [hN, mul_assoc, Nat.mul_div_cancel_left _ hpos]
  rw [Finset.sum_congr rfl (fun e _ ↦ hterm e), ← Finset.mul_sum, h, hN, mul_comm]

theorem word1_zero (z : Fin (2 ^ (1 - 1))) : z = 0 := by
  have h1 := z.isLt
  simp only [pow_zero] at h1
  exact Fin.ext (by omega)

theorem hmass2 (i : Fin 3) (c : Cell (2 * 2 ^ (1 - 1)) 1104 parent2) :
    ∑ w, mu2 i c w = m2 c.1 c.2 + m2 c.1 (complement (htotal2 c.1) c.2) := by
  classical
  have hv : (c.2.val i).val < 3 := by have := c.2.property.1; omega
  rw [Finset.sum_eq_single_of_mem (fun _ ↦ (⟨(c.2.val i).val, hv⟩ : Fin 3))
    (Finset.mem_univ _)]
  · simp [mu2]
  · intro w _ hne
    unfold mu2
    rw [if_neg]
    intro h
    apply hne
    funext z
    rw [word1_zero z]
    exact Fin.ext h

theorem hsupport2 (i : Fin 3) (c : Cell (2 * 2 ^ (1 - 1)) 1104 parent2)
    (w : CompleteSplit.CompleteWord 1) (h : 0 < mu2 i c w) : ∑ z, (w z).val = (c.2.val i).val := by
  unfold mu2 at h
  split_ifs at h with hw
  · simpa using hw
  · simp at h

theorem hboundary2 : BoundaryProfiles mu2 := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · intro c hc w
    unfold mu2
    have h0 := c.2.property.1
    have h1 : (c.2.val 0).val ≤ 2 := by omega
    have h2 : (c.2.val 1).val ≤ 2 := by omega
    have h3 : (c.2.val 2).val ≤ 2 := by omega
    have hw : (w 0).val ≤ 2 := by omega
    simp only [Fin.rev]
    congr 1
    simp only [eq_iff_iff]
    constructor <;> intro h <;> simp only [Fin.val_mk] at * <;> omega

end MME.ReleasedRecursive


open MME.ReleasedRecursive in
theorem solution :
    (∀ (ρ : Fin 6) (i : Fin 3) (c : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 ρ)),
      ∑ w, mu3 ρ i c w = m3 ρ c.1 c.2 + m3 ρ c.1 (complement (htotal3 ρ c.1) c.2)) ∧
    (∀ (i : Fin 3) (c : Cell (2 * 2 ^ (1 - 1)) 1104 parent2),
      ∑ w, mu2 i c w = m2 c.1 c.2 + m2 c.1 (complement (htotal2 c.1) c.2)) ∧
    (∀ (i : Fin 3) (c : Cell (2 * 2 ^ (1 - 1)) 1104 parent2) (w : CompleteSplit.CompleteWord 1),
      0 < mu2 i c w → ∑ z, (w z).val = (c.2.val i).val) ∧
    BoundaryProfiles mu2 :=
  ⟨hmass3, hmass2, hsupport2, hboundary2⟩
