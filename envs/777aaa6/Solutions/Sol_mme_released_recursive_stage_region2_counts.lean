-- Prove2me | solution 1 for mme_released_recursive_stage_region2_counts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-22T18:26:57.61128+00:00
-- url     : https://prove2.me/submissions/f3e91a83-3889-45e7-ab86-785c6d78c2b5

import Mathlib
import Definitions.Def_mme_released_recursive_stage_data
import Definitions.Def_mme_recursive_yz_owned_filters
open BigOperators MME MME.RecursiveYZ MME.RecStage
set_option autoImplicit false
set_option maxHeartbeats 4000000


open BigOperators MME MME.RecursiveYZ MME.RecStage
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace MME.RecStage

/-- Each child distribution sums to `D` over the nine complete level-2 words. -/
theorem childW_sum' (x y s0 k : ℕ) (hs : x + y ≤ 4) (hk : k < 3) (h0 : 2 * s0 ≤ D) :
    ∑ a : Fin 3, ∑ b : Fin 3, childW x y (4 - x - y) s0 k a.val b.val = D := by
  have hx : x ≤ 4 := by omega
  have hy : y ≤ 4 := by omega
  interval_cases x <;> interval_cases y <;> interval_cases k <;>
    simp [childW, jw, elemT, coord, Fin.sum_univ_three, D] at h0 hs ⊢ <;> omega

theorem childW_sum (x y z s0 k : ℕ) (hs : x + y + z = 4) (hk : k < 3) (h0 : 2 * s0 ≤ D) :
    ∑ a : Fin 3, ∑ b : Fin 3, childW x y z s0 k a.val b.val = D := by
  obtain rfl : z = 4 - x - y := by omega
  exact childW_sum' x y s0 k (by omega) hk h0

/-- The guard of a nonzero split weight. -/
theorem jw_ne_zero (a0 a1 a2 s0 e0 e1 e2 : ℕ) (h : jw a0 a1 a2 s0 e0 e1 e2 ≠ 0) :
    e0 ≤ a0 ∧ e1 ≤ a1 ∧ e2 ≤ a2 := by
  unfold jw at h
  by_cases hg : e0 ≤ a0 ∧ e1 ≤ a1 ∧ e2 ≤ a2 ∧ a0 - e0 ≤ 2 ∧ a1 - e1 ≤ 2 ∧ a2 - e2 ≤ 2
  · exact ⟨hg.1, hg.2.1, hg.2.2.1⟩
  · rw [if_neg hg] at h
    exact absurd rfl h

theorem coord_add (x y z e0 e1 e2 k : ℕ) (hk : k < 3) (h0 : e0 ≤ x) (h1 : e1 ≤ y) (h2 : e2 ≤ z) :
    coord k (e0, e1, e2) + coord k (x - e0, y - e1, z - e2) = coord k (x, y, z) := by
  match k, hk with
  | 0, _ => simp only [coord]; norm_num; omega
  | 1, _ => simp only [coord]; norm_num; omega
  | 2, _ => simp only [coord]; norm_num; omega

/-- A child word weight vanishes unless the two letters' grades add up to the cell's grade. -/
theorem childW_support (x y z s0 k w0 w1 : ℕ) (hk : k < 3)
    (h : childW x y z s0 k w0 w1 ≠ 0) : w0 + w1 = coord k (x, y, z) := by
  unfold childW at h
  have hex : ∃ e ∈ elemT, (if coord k e = w0 ∧ coord k (x - e.1, y - e.2.1, z - e.2.2) = w1 then
      jw x y z s0 e.1 e.2.1 e.2.2 else 0) ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact h (List.sum_eq_zero (by
      intro v hv
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hv
      exact hc e he))
  obtain ⟨e, _, hne⟩ := hex
  obtain ⟨e0, e1, e2⟩ := e
  split_ifs at hne with hcond
  · obtain ⟨h0, h1, h2⟩ := jw_ne_zero _ _ _ _ _ _ _ hne
    obtain ⟨hw0, hw1⟩ := hcond
    subst hw0
    subst hw1
    exact coord_add x y z e0 e1 e2 k hk h0 h1 h2
  · exact absurd rfl hne

end MME.RecStage


open BigOperators MME MME.RecursiveYZ MME.RecStage
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace MME.RecStage

theorem getD_range9 (f : ℕ → ℕ) (k : ℕ) (hk : k < 9) : ((List.range 9).map f).getD k 0 = f k := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk]
  simp

/-- Sum over complete level-2 words as a double sum over the two letters. -/
theorem sum_word2 (f : ℕ → ℕ → ℕ) :
    ∑ w : CompleteSplit.CompleteWord 2, f (w 0).val (w 1).val =
      ∑ a : Fin 3, ∑ b : Fin 3, f a.val b.val := by
  rw [← Fintype.sum_prod_type']
  exact Fintype.sum_equiv (finTwoArrowEquiv (Fin 3)) _ _ (fun _ ↦ rfl)

theorem m3_dvd (ρ : Fin 6) (r : Fin 88) (c) : D ∣ m3 ρ r c := by
  unfold m3
  exact Dvd.dvd.mul_left (dvd_pow_self _ (by norm_num)) _

/-- Mass condition of the level-3 histograms, given the cell split parameters are at most `D/2`. -/
theorem hmass3_of_s0 (ρ : Fin 6) (i : Fin 3) (c : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 ρ))
    (hs0 : 2 * (cellRec ρ c.1 c.2).2 ≤ D) :
    ∑ w, mu3 ρ i c w = m3 ρ c.1 c.2 + m3 ρ c.1 (complement (htotal3 ρ c.1) c.2) := by
  classical
  set M := m3 ρ c.1 c.2 + m3 ρ c.1 (complement (htotal3 ρ c.1) c.2) with hM
  obtain ⟨M', hM'⟩ : D ∣ M := dvd_add (m3_dvd _ _ _) (m3_dvd _ _ _)
  have hpos : 0 < D := by norm_num [D]
  have hsum : (c.2.val 0).val + (c.2.val 1).val + (c.2.val 2).val = 4 := c.2.property.1
  have hkey := childW_sum (c.2.val 0).val (c.2.val 1).val (c.2.val 2).val (cellRec ρ c.1 c.2).2
    i.val hsum i.isLt hs0
  have hentry : ∀ w : CompleteSplit.CompleteWord 2,
      (cellDist ρ i c.1 c.2).getD (3 * (w 0).val + (w 1).val) 0 =
      childW (c.2.val 0).val (c.2.val 1).val (c.2.val 2).val (cellRec ρ c.1 c.2).2 i.val
        (w 0).val (w 1).val := by
    intro w
    have h0 := (w 0).isLt
    have h1 := (w 1).isLt
    unfold cellDist
    rw [getD_range9 _ _ (by omega)]
    congr 1
    · omega
    · omega
  unfold mu3
  rw [← hM, hM']
  have hterm : ∀ w : CompleteSplit.CompleteWord 2,
      D * M' * (cellDist ρ i c.1 c.2).getD (3 * (w 0).val + (w 1).val) 0 / D =
      M' * childW (c.2.val 0).val (c.2.val 1).val (c.2.val 2).val (cellRec ρ c.1 c.2).2 i.val
        (w 0).val (w 1).val := by
    intro w
    rw [hentry w, mul_assoc, Nat.mul_div_cancel_left _ hpos]
  rw [Finset.sum_congr rfl (fun w _ ↦ hterm w), ← Finset.mul_sum,
    sum_word2 (fun a b ↦ childW _ _ _ _ i.val a b), hkey, mul_comm]

theorem n3_eq (ρ : Fin 6) (r : Fin 88) : n3 ρ r = wAt ρ r * D ^ 3 := rfl

theorem hn3_of_pos (ρ : Fin 6) (r : Fin 88) (h : 0 < wAt ρ r) : 0 < n3 ρ r := by
  rw [n3_eq]
  exact Nat.mul_pos h (by norm_num [D])

theorem hm3_of_alpha (ρ : Fin 6) (r : Fin 88)
    (h : ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (2 - 1)) (parent3 ρ r), (cellRec ρ r c).1 = D) :
    ∑ c, m3 ρ r c = n3 ρ r := by
  unfold m3
  rw [show (fun c : RecursiveThinSplit.Split (2 * 2 ^ (2 - 1)) (parent3 ρ r) ↦
      wAt ρ r * (cellRec ρ r c).1 * D ^ 2) =
    (fun c ↦ (wAt ρ r * D ^ 2) * (cellRec ρ r c).1) from funext fun c ↦ by ring,
    ← Finset.mul_sum, h, n3_eq]
  ring

theorem n2_dvd (r : Fin 1104) : D ∣ n2 r := Dvd.dvd.mul_left (dvd_pow_self _ (by norm_num)) _

theorem hm2_of_weights (r : Fin 1104)
    (h : ∑ e : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 r),
      jw (parent2 r 0) (parent2 r 1) (parent2 r 2) (l2At r).2.2
        (e.val 0).val (e.val 1).val (e.val 2).val = D) :
    ∑ e, m2 r e = n2 r := by
  unfold m2 n2
  rw [show (fun e : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 r) ↦
      (l2At r).2.1 * jw (parent2 r 0) (parent2 r 1) (parent2 r 2) (l2At r).2.2
        (e.val 0).val (e.val 1).val (e.val 2).val * D) =
    (fun e ↦ ((l2At r).2.1 * D) * jw (parent2 r 0) (parent2 r 1) (parent2 r 2) (l2At r).2.2
        (e.val 0).val (e.val 1).val (e.val 2).val) from funext fun e ↦ by ring,
    ← Finset.mul_sum, h]
  ring

theorem word1_zero (z : Fin (2 ^ (1 - 1))) : z = 0 := by
  have h1 := z.isLt
  simp only [pow_zero] at h1
  exact Fin.ext (by omega)

theorem hmass2 (i : Fin 3) (c : Cell (2 * 2 ^ (1 - 1)) 1104 parent2) :
    ∑ w, mu2 i c w = m2 c.1 c.2 + m2 c.1 (complement (htotal2 c.1) c.2) := by
  classical
  have hv : (c.2.val i).val < 3 := by have := c.2.property.1; omega
  rw [Finset.sum_eq_single_of_mem (fun _ ↦ (⟨(c.2.val i).val, hv⟩ : Fin 3)) (Finset.mem_univ _)]
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

end MME.RecStage

namespace MME.RecStage

set_option maxHeartbeats 0 in
private theorem wpos_2 : ∀ r : Fin 88, 0 < wAt 2 r := by decide +kernel

set_option maxHeartbeats 0 in
private theorem asum_2 : ∀ r : Fin 88,
    ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (2 - 1)) (parent3 2 r), (cellRec 2 r c).1 = D := by
  decide +kernel

end MME.RecStage

open MME.RecStage in
theorem solution : (∀ r, 0 < n3 2 r) ∧ ∀ r, ∑ c, m3 2 r c = n3 2 r :=
  ⟨fun r ↦ hn3_of_pos _ r (wpos_2 r), fun r ↦ hm3_of_alpha _ r (asum_2 r)⟩
