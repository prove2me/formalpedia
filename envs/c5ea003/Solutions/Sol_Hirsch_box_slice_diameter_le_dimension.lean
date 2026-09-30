-- Prove2me | solution 1 for Hirsch.box_slice_diameter_le_dimension
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-08T14:39:41.659232+00:00
-- url     : https://prove2.me/submissions/937ecd3d-cece-4a21-9b52-20851edabd23

import Definitions.Def_Hirsch_model
import Mathlib
-- BEGIN Solutions/BoxSliceExchange.lean

open Set Hirsch
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace HirschBoxSlice
variable {d : ℕ}

def slice (cap : Fin d → ℝ) (total : ℝ) : Set (Fin d → ℝ) :=
  {x | (∀ k, 0 ≤ x k ∧ x k ≤ cap k) ∧ ∑ k, x k = total}

def exchange (x : Fin d → ℝ) (p q : Fin d) (ε : ℝ) : Fin d → ℝ :=
  fun k => x k + (if k = p then ε else 0) - (if k = q then ε else 0)

lemma exchange_at_p (x : Fin d → ℝ) (p q : Fin d) (hpq : p ≠ q) (ε : ℝ) :
    exchange x p q ε p = x p + ε := by simp [exchange, hpq]
lemma exchange_at_q (x : Fin d → ℝ) (p q : Fin d) (hpq : p ≠ q) (ε : ℝ) :
    exchange x p q ε q = x q - ε := by simp [exchange, hpq.symm]
lemma exchange_elsewhere (x : Fin d → ℝ) (p q k : Fin d)
    (hkp : k ≠ p) (hkq : k ≠ q) (ε : ℝ) :
    exchange x p q ε k = x k := by simp [exchange, hkp, hkq]
lemma exchange_sum (x : Fin d → ℝ) (p q : Fin d) (ε : ℝ) :
    (∑ k, exchange x p q ε k) = ∑ k, x k := by
  simp [exchange, Finset.sum_sub_distrib, Finset.sum_add_distrib]

lemma exchange_mem (cap : Fin d → ℝ) (total : ℝ)
    (x : Fin d → ℝ) (p q : Fin d) (hpq : p ≠ q)
    (hx : x ∈ slice cap total) (ε : ℝ)
    (hε0 : 0 ≤ ε) (hεp : ε ≤ cap p - x p) (hεq : ε ≤ x q) :
    exchange x p q ε ∈ slice cap total := by
  refine ⟨?_, (exchange_sum x p q ε).trans hx.2⟩
  intro k
  by_cases hkp : k = p
  · subst k
    rw [exchange_at_p x p q hpq ε]
    constructor <;> linarith [(hx.1 p).1, (hx.1 p).2]
  · by_cases hkq : k = q
    · subst k
      rw [exchange_at_q x p q hpq ε]
      constructor <;> linarith [(hx.1 q).1, (hx.1 q).2]
    · rw [exchange_elsewhere x p q k hkp hkq ε]
      exact hx.1 k

lemma two_coordinate_sum (x z : Fin d → ℝ) (p q : Fin d) (hpq : p ≠ q)
    (hsum : (∑ k, z k) = ∑ k, x k)
    (hother : ∀ k, k ≠ p → k ≠ q → z k = x k) :
    z p + z q = x p + x q := by
  classical
  let S : Finset (Fin d) := Finset.univ.erase p
  have hqS : q ∈ S := by simp [S, hpq.symm]
  have hx1 := Finset.sum_erase_add Finset.univ x (Finset.mem_univ p)
  have hz1 := Finset.sum_erase_add Finset.univ z (Finset.mem_univ p)
  have hx2 := Finset.sum_erase_add S x hqS
  have hz2 := Finset.sum_erase_add S z hqS
  have hrest : (∑ k ∈ S.erase q, z k) = ∑ k ∈ S.erase q, x k := by
    apply Finset.sum_congr rfl
    intro k hk
    have hne : k ≠ q ∧ k ≠ p := by simpa [S] using hk
    exact hother k hne.2 hne.1
  dsimp [S] at hx2 hz2 hrest
  linarith

/-- A maximal two-coordinate transfer is an actual edge, not only a circuit. -/
lemma maximal_exchange_is_edge
    (cap : Fin d → ℝ) (total : ℝ) (x : Fin d → ℝ)
    (p q : Fin d) (hpq : p ≠ q) (hx : x ∈ slice cap total)
    (hfixed : ∀ k, k ≠ p → k ≠ q → x k = 0 ∨ x k = cap k)
    (hstart : x p = 0 ∨ x q = cap q)
    (hpositive : 0 < min (cap p - x p) (x q)) :
    Adj (slice cap total) x (exchange x p q (min (cap p - x p) (x q))) := by
  classical
  let ε : ℝ := min (cap p - x p) (x q)
  let y := exchange x p q ε
  have hε : 0 < ε := hpositive
  have hyp : y p = x p + ε := exchange_at_p x p q hpq ε
  have hyq : y q = x q - ε := exchange_at_q x p q hpq ε
  have hyo : ∀ k, k ≠ p → k ≠ q → y k = x k := by
    intro k hkp hkq
    exact exchange_elsewhere x p q k hkp hkq ε
  have hy : y ∈ slice cap total :=
    exchange_mem cap total x p q hpq hx ε hε.le (min_le_left _ _) (min_le_right _ _)
  have hfinish : y p = cap p ∨ y q = 0 := by
    rcases le_total (cap p - x p) (x q) with h | h
    · have heq : ε = cap p - x p := min_eq_left h
      exact Or.inl (by rw [hyp, heq]; ring)
    · have heq : ε = x q := min_eq_right h
      exact Or.inr (by rw [hyq, heq]; ring)
  let F : Set (Fin d → ℝ) :=
    {z | z ∈ slice cap total ∧ ∀ k, k ≠ p → k ≠ q → z k = x k}
  have hFext : IsExtreme ℝ (slice cap total) F := by
    refine ⟨fun z hz => hz.1, ?_⟩
    intro r hr s hs z hz hopen
    refine ⟨hr, ?_⟩
    intro k hkp hkq
    obtain ⟨α, β, hα, hβ, hαβ, hcombo⟩ := hopen
    have hcoord := congrFun hcombo k
    change α * r k + β * s k = z k at hcoord
    have hpin : z k = x k := hz.2 k hkp hkq
    rw [hpin] at hcoord
    rcases hfixed k hkp hkq with hk0 | hkcap
    · rw [hk0] at hcoord ⊢
      have hr0 := (hr.1 k).1
      have hs0 := (hs.1 k).1
      by_contra hrne
      have hrpos : 0 < r k := lt_of_le_of_ne hr0 (Ne.symm hrne)
      have hprod := mul_pos hα hrpos
      linarith [mul_nonneg hβ.le hs0]
    · rw [hkcap] at hcoord ⊢
      have hrle := (hr.1 k).2
      have hsle := (hs.1 k).2
      have hweight : α * cap k + β * cap k = cap k := by rw [← add_mul, hαβ, one_mul]
      by_contra hrne
      have hrlt : r k < cap k := lt_of_le_of_ne hrle hrne
      have hprod := mul_pos hα (sub_pos.mpr hrlt)
      nlinarith [mul_nonneg hβ.le (sub_nonneg.mpr hsle)]
  have hFsub : F ⊆ segment ℝ x y := by
    intro z hz
    have hsum : z p + z q = x p + x q :=
      two_coordinate_sum x z p q hpq (hz.1.2.trans hx.2.symm) hz.2
    let t : ℝ := (z p - x p) / ε
    have hzp : z p = x p + t * ε := by
      dsimp [t]
      rw [div_mul_cancel₀ _ hε.ne']
      ring
    have hzq : z q = x q - t * ε := by linarith
    have ht0 : 0 ≤ t := by
      by_contra ht
      have htneg : t < 0 := lt_of_not_ge ht
      have hmul : t * ε < 0 := mul_neg_of_neg_of_pos htneg hε
      rcases hstart with hp0 | hqc
      · have hzlo := (hz.1.1 p).1
        rw [hp0] at hzp
        nlinarith
      · have hzhi := (hz.1.1 q).2
        rw [hqc] at hzq
        nlinarith
    have ht1 : t ≤ 1 := by
      by_contra ht
      have htgt : 1 < t := lt_of_not_ge ht
      have hmul := mul_pos (sub_pos.mpr htgt) hε
      rcases hfinish with hpc | hq0
      · have hzhi := (hz.1.1 p).2
        rw [hyp] at hpc
        nlinarith
      · have hzlo := (hz.1.1 q).1
        rw [hyq] at hq0
        nlinarith
    refine ⟨1 - t, t, sub_nonneg.mpr ht1, ht0, by ring, ?_⟩
    funext k
    change (1 - t) * x k + t * y k = z k
    by_cases hkp : k = p
    · subst k
      rw [hyp, hzp]
      ring
    · by_cases hkq : k = q
      · subst k
        rw [hyq, hzq]
        ring
      · rw [hyo k hkp hkq, hz.2 k hkp hkq]
        ring
  have hsegF : segment ℝ x y ⊆ F := by
    intro z hz
    obtain ⟨α, β, hα, hβ, hαβ, hcombo⟩ := hz
    have hcoord : ∀ k, z k = α * x k + β * y k := by
      intro k
      exact (congrFun hcombo k).symm
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro k
      rw [hcoord k]
      constructor
      · exact add_nonneg (mul_nonneg hα (hx.1 k).1) (mul_nonneg hβ (hy.1 k).1)
      · calc
          α * x k + β * y k ≤ α * cap k + β * cap k :=
            add_le_add (mul_le_mul_of_nonneg_left (hx.1 k).2 hα)
              (mul_le_mul_of_nonneg_left (hy.1 k).2 hβ)
          _ = cap k := by rw [← add_mul, hαβ, one_mul]
    · rw [← hcombo]
      change (∑ k, (α * x k + β * y k)) = total
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        hx.2, hy.2, ← add_mul, hαβ, one_mul]
    · intro k hkp hkq
      rw [hcoord k, hyo k hkp hkq, ← add_mul, hαβ, one_mul]
  have hne : x ≠ y := by
    intro heq
    have h := congrFun heq p
    rw [hyp] at h
    linarith
  have hFeq : F = segment ℝ x y := Set.Subset.antisymm hFsub hsegF
  exact ⟨hne, hFeq ▸ hFext⟩
end HirschBoxSlice
end


-- BEGIN Solutions/BoxSliceVertex.lean
open Set Hirsch HirschBoxSlice
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace HirschBoxSlice
variable {d : ℕ}

lemma extreme_at_most_one_interior
    (cap : Fin d → ℝ) (total : ℝ) (x : Fin d → ℝ)
    (hx : x ∈ extremePoints ℝ (slice cap total))
    (p q : Fin d) (hp0 : 0 < x p) (hp1 : x p < cap p)
    (hq0 : 0 < x q) (hq1 : x q < cap q) : p = q := by
  by_contra hpq
  let ε : ℝ := min (min (x p) (cap p - x p)) (min (x q) (cap q - x q))
  have hε : 0 < ε :=
    lt_min (lt_min hp0 (sub_pos.mpr hp1)) (lt_min hq0 (sub_pos.mpr hq1))
  have hεp0 : ε ≤ x p := (min_le_left _ _).trans (min_le_left _ _)
  have hεp1 : ε ≤ cap p - x p := (min_le_left _ _).trans (min_le_right _ _)
  have hεq0 : ε ≤ x q := (min_le_right _ _).trans (min_le_left _ _)
  have hεq1 : ε ≤ cap q - x q := (min_le_right _ _).trans (min_le_right _ _)
  let a := exchange x p q ε
  let b := exchange x q p ε
  have ha : a ∈ slice cap total := exchange_mem cap total x p q hpq hx.1 ε hε.le hεp1 hεq0
  have hb : b ∈ slice cap total := exchange_mem cap total x q p (Ne.symm hpq) hx.1 ε hε.le hεq1 hεp0
  have hop : x ∈ openSegment ℝ a b := by
    refine ⟨(1 / 2 : ℝ), (1 / 2 : ℝ), by norm_num, by norm_num, by norm_num, ?_⟩
    funext k
    change (1 / 2 : ℝ) * a k + (1 / 2 : ℝ) * b k = x k
    dsimp [a, b, exchange]
    split_ifs <;> ring
  have hax : a = x := hx.2 ha hb hop
  have heq := congrFun hax p
  have hval : a p = x p + ε := exchange_at_p x p q hpq ε
  rw [hval] at heq
  linarith

lemma extreme_of_bound_except
    (cap : Fin d → ℝ) (total : ℝ) (x : Fin d → ℝ)
    (hx : x ∈ slice cap total) (j : Fin d)
    (hfixed : ∀ k, k ≠ j → x k = 0 ∨ x k = cap k) :
    x ∈ extremePoints ℝ (slice cap total) := by
  refine ⟨hx, ?_⟩
  intro y hy z hz hop
  obtain ⟨α, β, hα, hβ, hαβ, hcombo⟩ := hop
  have heq : ∀ k, k ≠ j → y k = x k := by
    intro k hkj
    have hc := congrFun hcombo k
    change α * y k + β * z k = x k at hc
    rcases hfixed k hkj with hx0 | hxc
    · rw [hx0] at hc ⊢
      by_contra hne
      have hpos : 0 < y k := lt_of_le_of_ne (hy.1 k).1 (Ne.symm hne)
      have hp := mul_pos hα hpos
      linarith [mul_nonneg hβ.le (hz.1 k).1]
    · rw [hxc] at hc ⊢
      by_contra hne
      have hlt : y k < cap k := lt_of_le_of_ne (hy.1 k).2 hne
      have hp := mul_pos hα (sub_pos.mpr hlt)
      have hw : α * cap k + β * cap k = cap k := by rw [← add_mul, hαβ, one_mul]
      nlinarith [mul_nonneg hβ.le (sub_nonneg.mpr (hz.1 k).2)]
  have hrest : (∑ k ∈ Finset.univ.erase j, y k) = ∑ k ∈ Finset.univ.erase j, x k := by
    apply Finset.sum_congr rfl
    intro k hk
    exact heq k (Finset.ne_of_mem_erase hk)
  have hsx := Finset.sum_erase_add Finset.univ x (Finset.mem_univ j)
  have hsy := Finset.sum_erase_add Finset.univ y (Finset.mem_univ j)
  have hj : y j = x j := by linarith [hx.2, hy.2]
  funext k
  by_cases hkj : k = j
  · simpa only [hkj] using hj
  · exact heq k hkj
end HirschBoxSlice
end


-- BEGIN Solutions/BoxSlicePivotBasics.lean
open Set Hirsch
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace HirschBoxSlice
variable {d : ℕ}

def AtBound (cap x : Fin d → ℝ) (k : Fin d) : Prop := x k = 0 ∨ x k = cap k
def Inside (cap x : Fin d → ℝ) (k : Fin d) : Prop := 0 < x k ∧ x k < cap k
def Regular (cap x : Fin d → ℝ) : Prop :=
  ∀ p q, Inside cap x p → Inside cap x q → p = q

def Inc (v : Fin d → ℝ) (j : Fin d) (x : Fin d → ℝ) : Prop :=
  ∃ k, k ≠ j ∧ x k < v k
def Dec (v : Fin d → ℝ) (j : Fin d) (x : Fin d → ℝ) : Prop :=
  ∃ k, k ≠ j ∧ v k < x k
def Mixed (cap v : Fin d → ℝ) (j : Fin d) (x : Fin d → ℝ) : Prop :=
  Inside cap x j ∧ Inc v j x ∧ Dec v j x
noncomputable def mismatches (v : Fin d → ℝ) (j : Fin d) (x : Fin d → ℝ) : Finset (Fin d) := by
  classical
  exact Finset.univ.filter (fun k => k ≠ j ∧ x k ≠ v k)
noncomputable def potential (cap v : Fin d → ℝ) (j : Fin d) (x : Fin d → ℝ) : ℕ := by
  classical
  exact (mismatches v j x).card + if Mixed cap v j x then 1 else 0

def Preserves (v : Fin d → ℝ) (j : Fin d) (x y : Fin d → ℝ) : Prop :=
  ∀ k, k ≠ j → x k = v k → y k = v k

lemma regular_of_extreme (cap : Fin d → ℝ) (total : ℝ) (x : Fin d → ℝ)
    (hx : x ∈ extremePoints ℝ (slice cap total)) : Regular cap x := by
  intro p q hp hq
  exact extreme_at_most_one_interior cap total x hx p q hp.1 hp.2 hq.1 hq.2

lemma bound_of_not_inside (cap : Fin d → ℝ) (total : ℝ) (x : Fin d → ℝ)
    (hx : x ∈ slice cap total) (k : Fin d) (hk : ¬ Inside cap x k) : AtBound cap x k := by
  by_cases hz : x k = 0
  · exact Or.inl hz
  · right
    by_contra hh
    exact hk ⟨lt_of_le_of_ne (hx.1 k).1 (Ne.symm hz), lt_of_le_of_ne (hx.1 k).2 hh⟩

lemma not_inside_of_bound {cap x : Fin d → ℝ} {k : Fin d}
    (h : AtBound cap x k) : ¬ Inside cap x k := by
  rintro ⟨h0, h1⟩
  rcases h with h | h <;> linarith

lemma bounds_except_inside (cap : Fin d → ℝ) (total : ℝ) (x : Fin d → ℝ)
    (hx : x ∈ slice cap total) (hr : Regular cap x)
    (k : Fin d) (hk : Inside cap x k) : ∀ l, l ≠ k → AtBound cap x l := by
  intro l hl
  exact bound_of_not_inside cap total x hx l (fun hi => hl (hr l k hi hk))

lemma target_upper_of_inc (cap : Fin d → ℝ) (total : ℝ) (x v : Fin d → ℝ)
    (hx : x ∈ slice cap total) {p : Fin d}
    (hb : AtBound cap v p) (hp : x p < v p) : v p = cap p := by
  rcases hb with hb | hb
  · have h0 := (hx.1 p).1
    linarith
  · exact hb
lemma target_lower_of_dec (cap : Fin d → ℝ) (total : ℝ) (x v : Fin d → ℝ)
    (hx : x ∈ slice cap total) {q : Fin d}
    (hb : AtBound cap v q) (hq : v q < x q) : v q = 0 := by
  rcases hb with hb | hb
  · exact hb
  · have h1 := (hx.1 q).2
    linarith

lemma eq_of_no_signs (total : ℝ) (cap x v : Fin d → ℝ) (j : Fin d)
    (hx : x ∈ slice cap total) (hv : v ∈ slice cap total)
    (hi : ¬ Inc v j x) (hd : ¬ Dec v j x) : x = v := by
  have heq : ∀ k, k ≠ j → x k = v k := by
    intro k hk
    apply le_antisymm
    · exact le_of_not_gt (fun h => hd ⟨k, hk, h⟩)
    · exact le_of_not_gt (fun h => hi ⟨k, hk, h⟩)
  have hr : (∑ k ∈ Finset.univ.erase j, x k) = ∑ k ∈ Finset.univ.erase j, v k :=
    Finset.sum_congr rfl (fun k hk => heq k (Finset.ne_of_mem_erase hk))
  have hsx := Finset.sum_erase_add Finset.univ x (Finset.mem_univ j)
  have hsv := Finset.sum_erase_add Finset.univ v (Finset.mem_univ j)
  have hj : x j = v j := by linarith [hx.2, hv.2]
  funext k
  by_cases hk : k = j
  · simpa only [hk] using hj
  · exact heq k hk

lemma potential_le_dim (cap v x : Fin d → ℝ) (j : Fin d) : potential cap v j x ≤ d := by
  classical
  have hs : mismatches v j x ⊆ Finset.univ.erase j := by
    intro k hk
    have h := (Finset.mem_filter.mp hk).2.1
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    exact h
  have hc := Finset.card_le_card hs
  have hj : 0 < d := j.pos
  have hc' : (mismatches v j x).card ≤ d - 1 := by simpa using hc
  unfold potential
  split_ifs <;> omega

lemma mismatch_subset {v x y : Fin d → ℝ} {j : Fin d}
    (hp : Preserves v j x y) : mismatches v j y ⊆ mismatches v j x := by
  classical
  intro k hk
  have hk' := (Finset.mem_filter.mp hk).2
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, hk'.1, ?_⟩
  intro h
  exact hk'.2 (hp k hk'.1 h)

lemma mismatch_card_lt {v x y : Fin d → ℝ} {j : Fin d}
    (hp : Preserves v j x y)
    (hit : ∃ k, k ≠ j ∧ x k ≠ v k ∧ y k = v k) :
    (mismatches v j y).card < (mismatches v j x).card := by
  classical
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨mismatch_subset hp, ?_⟩
  intro heq
  obtain ⟨k, hkj, hkx, hky⟩ := hit
  have hk : k ∈ mismatches v j x := by simp [mismatches, hkj, hkx]
  rw [← heq] at hk
  exact (Finset.mem_filter.mp hk).2.2 hky

lemma signs_preserved (cap : Fin d → ℝ) (total : ℝ) (x y v : Fin d → ℝ) (j : Fin d)
    (hx : x ∈ slice cap total) (hy : y ∈ slice cap total)
    (hv : ∀ k, k ≠ j → AtBound cap v k) (hp : Preserves v j x y) :
    (Inc v j y → Inc v j x) ∧ (Dec v j y → Dec v j x) := by
  constructor
  · rintro ⟨k, hkj, hki⟩
    have hvc := target_upper_of_inc cap total y v hy (hv k hkj) hki
    refine ⟨k, hkj, ?_⟩
    have hle : x k ≤ v k := by rw [hvc]; exact (hx.1 k).2
    apply lt_of_le_of_ne hle
    intro heq
    have := hp k hkj heq
    linarith
  · rintro ⟨k, hkj, hkd⟩
    have hv0 := target_lower_of_dec cap total y v hy (hv k hkj) hkd
    refine ⟨k, hkj, ?_⟩
    have hle : v k ≤ x k := by rw [hv0]; exact (hx.1 k).1
    apply lt_of_le_of_ne hle
    intro heq
    have := hp k hkj heq.symm
    linarith

lemma potential_drop_hit {cap v x y : Fin d → ℝ} {j : Fin d}
    (hp : Preserves v j x y)
    (hit : ∃ k, k ≠ j ∧ x k ≠ v k ∧ y k = v k)
    (hm : Mixed cap v j y → Mixed cap v j x) :
    potential cap v j y < potential cap v j x := by
  classical
  have hc := mismatch_card_lt hp hit
  unfold potential
  by_cases hx : Mixed cap v j x <;> by_cases hy : Mixed cap v j y
  · simp only [if_pos hx, if_pos hy]; omega
  · simp only [if_pos hx, if_neg hy]; omega
  · exact False.elim (hx (hm hy))
  · simp only [if_neg hx, if_neg hy]; exact hc

lemma potential_drop_break {cap v x y : Fin d → ℝ} {j : Fin d}
    (hp : Preserves v j x y) (hx : Mixed cap v j x) (hy : ¬ Mixed cap v j y) :
    potential cap v j y < potential cap v j x := by
  classical
  have hc := Finset.card_le_card (mismatch_subset hp)
  simp only [potential, if_pos hx, if_neg hy]
  omega

/-- A maximal feasible pivot from a regular point has an extreme endpoint. -/
lemma maximal_exchange_vertex (cap : Fin d → ℝ) (total : ℝ) (x : Fin d → ℝ)
    (p q : Fin d) (hpq : p ≠ q) (hx : x ∈ slice cap total) (hr : Regular cap x)
    (hfixed : ∀ k, k ≠ p → k ≠ q → AtBound cap x k)
    (hpos : 0 < min (cap p - x p) (x q)) :
    let y := exchange x p q (min (cap p - x p) (x q))
    y ∈ extremePoints ℝ (slice cap total) ∧ Adj (slice cap total) x y ∧
      (y p = cap p ∨ y q = 0) := by
  dsimp only
  let ε := min (cap p - x p) (x q)
  let y := exchange x p q ε
  change y ∈ extremePoints ℝ (slice cap total) ∧ Adj (slice cap total) x y ∧ _
  have hp1 : x p < cap p := by have := lt_of_lt_of_le hpos (min_le_left _ _); linarith
  have hq0 : 0 < x q := lt_of_lt_of_le hpos (min_le_right _ _)
  have hstart : x p = 0 ∨ x q = cap q := by
    by_cases hp0 : x p = 0
    · exact Or.inl hp0
    · right
      by_contra hq1
      exact hpq (hr p q ⟨lt_of_le_of_ne (hx.1 p).1 (Ne.symm hp0), hp1⟩
        ⟨hq0, lt_of_le_of_ne (hx.1 q).2 hq1⟩)
  have hy : y ∈ slice cap total :=
    exchange_mem cap total x p q hpq hx ε hpos.le (min_le_left _ _) (min_le_right _ _)
  have hedge : Adj (slice cap total) x y :=
    maximal_exchange_is_edge cap total x p q hpq hx hfixed hstart hpos
  have hf : y p = cap p ∨ y q = 0 := by
    rcases le_total (cap p - x p) (x q) with h | h
    · left
      rw [show y p = x p + ε from exchange_at_p x p q hpq ε]
      dsimp [ε]
      rw [min_eq_left h]
      ring
    · right
      rw [show y q = x q - ε from exchange_at_q x p q hpq ε]
      dsimp [ε]
      rw [min_eq_right h]
      ring
  refine ⟨?_, hedge, hf⟩
  rcases hf with hp | hq
  · apply extreme_of_bound_except cap total y hy q
    intro k hkq
    by_cases hkp : k = p
    · exact Or.inr (by simpa only [hkp] using hp)
    · rw [show y k = x k from exchange_elsewhere x p q k hkp hkq ε]
      exact hfixed k hkp hkq
  · apply extreme_of_bound_except cap total y hy p
    intro k hkp
    by_cases hkq : k = q
    · exact Or.inl (by simpa only [hkq] using hq)
    · rw [show y k = x k from exchange_elsewhere x p q k hkp hkq ε]
      exact hfixed k hkp hkq
end HirschBoxSlice
end


-- BEGIN Solutions/BoxSlicePivotSelection.lean
open Set Hirsch
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace HirschBoxSlice
variable {d : ℕ}

lemma interior_ne_bound_target {cap x v : Fin d → ℝ} {k : Fin d}
    (hx : Inside cap x k) (hv : AtBound cap v k) : x k ≠ v k := by
  intro heq
  rcases hv with h | h <;> rcases hx with ⟨h0, h1⟩ <;> linarith

/-- With both mismatch signs present and the buffer at a bound, choose
opposite mismatches containing the possible interior coordinate. -/
lemma select_both (cap : Fin d → ℝ) (total : ℝ) (x v : Fin d → ℝ) (j : Fin d)
    (hx : x ∈ slice cap total) (hr : Regular cap x)
    (hv : ∀ k, k ≠ j → AtBound cap v k)
    (hj : AtBound cap x j) (hi : Inc v j x) (hd : Dec v j x) :
    ∃ p q : Fin d, p ≠ q ∧ p ≠ j ∧ q ≠ j ∧ x p < v p ∧ v q < x q ∧
      ∀ k, k ≠ p → k ≠ q → AtBound cap x k := by
  classical
  by_cases hf : ∃ k, Inside cap x k
  · obtain ⟨k, hk⟩ := hf
    have hkj : k ≠ j := by
      intro heq
      subst k
      exact not_inside_of_bound hj hk
    have hkv := interior_ne_bound_target hk (hv k hkj)
    rcases lt_or_gt_of_ne hkv with hki | hkd
    · obtain ⟨q, hqj, hq⟩ := hd
      have hkq : k ≠ q := by intro heq; subst q; linarith
      refine ⟨k, q, hkq, hkj, hqj, hki, hq, ?_⟩
      intro l hlk hlq
      exact bounds_except_inside cap total x hx hr k hk l hlk
    · obtain ⟨p, hpj, hp⟩ := hi
      have hpk : p ≠ k := by intro heq; subst p; linarith
      refine ⟨p, k, hpk, hpj, hkj, hp, hkd, ?_⟩
      intro l hlp hlk
      exact bounds_except_inside cap total x hx hr k hk l hlk
  · obtain ⟨p, hpj, hp⟩ := hi
    obtain ⟨q, hqj, hq⟩ := hd
    have hpq : p ≠ q := by intro heq; subst q; linarith
    refine ⟨p, q, hpq, hpj, hqj, hp, hq, ?_⟩
    intro k hkp hkq
    exact bound_of_not_inside cap total x hx k (fun hk => hf ⟨k, hk⟩)

lemma select_inc_buffer (cap : Fin d → ℝ) (total : ℝ) (x v : Fin d → ℝ) (j : Fin d)
    (hx : x ∈ slice cap total) (hr : Regular cap x)
    (hv : ∀ k, k ≠ j → AtBound cap v k)
    (hi : Inc v j x) (hd : ¬ Dec v j x) :
    ∃ p, p ≠ j ∧ x p < v p ∧ ∀ k, k ≠ p → k ≠ j → AtBound cap x k := by
  classical
  by_cases hf : ∃ k, k ≠ j ∧ Inside cap x k
  · obtain ⟨k, hkj, hk⟩ := hf
    have hkv := interior_ne_bound_target hk (hv k hkj)
    have hle : x k ≤ v k := le_of_not_gt (fun h => hd ⟨k, hkj, h⟩)
    refine ⟨k, hkj, lt_of_le_of_ne hle hkv, ?_⟩
    intro l hlk hlj
    exact bounds_except_inside cap total x hx hr k hk l hlk
  · obtain ⟨p, hpj, hp⟩ := hi
    refine ⟨p, hpj, hp, ?_⟩
    intro k hkp hkj
    exact bound_of_not_inside cap total x hx k (fun hk => hf ⟨k, hkj, hk⟩)

lemma select_dec_buffer (cap : Fin d → ℝ) (total : ℝ) (x v : Fin d → ℝ) (j : Fin d)
    (hx : x ∈ slice cap total) (hr : Regular cap x)
    (hv : ∀ k, k ≠ j → AtBound cap v k)
    (hi : ¬ Inc v j x) (hd : Dec v j x) :
    ∃ q, q ≠ j ∧ v q < x q ∧ ∀ k, k ≠ j → k ≠ q → AtBound cap x k := by
  classical
  by_cases hf : ∃ k, k ≠ j ∧ Inside cap x k
  · obtain ⟨k, hkj, hk⟩ := hf
    have hkv := interior_ne_bound_target hk (hv k hkj)
    have hle : v k ≤ x k := le_of_not_gt (fun h => hi ⟨k, hkj, h⟩)
    refine ⟨k, hkj, lt_of_le_of_ne hle hkv.symm, ?_⟩
    intro l hlj hlk
    exact bounds_except_inside cap total x hx hr k hk l hlk
  · obtain ⟨q, hqj, hq⟩ := hd
    refine ⟨q, hqj, hq, ?_⟩
    intro k hkj hkq
    exact bound_of_not_inside cap total x hx k (fun hk => hf ⟨k, hkj, hk⟩)

/-- If every nonbuffer mismatch needs an increase, the buffer has enough
mass to fill any one of them completely. A tie is harmless. -/
lemma inc_buffer_capacity (cap : Fin d → ℝ) (total : ℝ) (x v : Fin d → ℝ) (j p : Fin d)
    (hx : x ∈ slice cap total) (hv : v ∈ slice cap total)
    (hpj : p ≠ j) (hvp : v p = cap p) (hd : ¬ Dec v j x) :
    cap p - x p ≤ x j := by
  have hle : ∀ k, k ≠ j → x k ≤ v k :=
    fun k hk => le_of_not_gt (fun h => hd ⟨k, hk, h⟩)
  have hsx := Finset.sum_erase_add Finset.univ x (Finset.mem_univ j)
  have hsv := Finset.sum_erase_add Finset.univ v (Finset.mem_univ j)
  have hbalance : (∑ k ∈ Finset.univ.erase j, (v k - x k)) = x j - v j := by
    rw [Finset.sum_sub_distrib]
    linarith [hx.2, hv.2]
  have hcoord : v p - x p ≤ ∑ k ∈ Finset.univ.erase j, (v k - x k) :=
    Finset.single_le_sum (fun k hk => sub_nonneg.mpr (hle k (Finset.ne_of_mem_erase hk)))
      (by simp [hpj])
  have hvj := (hv.1 j).1
  rw [hvp] at hcoord
  linarith

lemma dec_buffer_capacity (cap : Fin d → ℝ) (total : ℝ) (x v : Fin d → ℝ) (j q : Fin d)
    (hx : x ∈ slice cap total) (hv : v ∈ slice cap total)
    (hqj : q ≠ j) (hvq : v q = 0) (hi : ¬ Inc v j x) :
    x q ≤ cap j - x j := by
  have hle : ∀ k, k ≠ j → v k ≤ x k :=
    fun k hk => le_of_not_gt (fun h => hi ⟨k, hk, h⟩)
  have hsx := Finset.sum_erase_add Finset.univ x (Finset.mem_univ j)
  have hsv := Finset.sum_erase_add Finset.univ v (Finset.mem_univ j)
  have hbalance : (∑ k ∈ Finset.univ.erase j, (x k - v k)) = v j - x j := by
    rw [Finset.sum_sub_distrib]
    linarith [hx.2, hv.2]
  have hcoord : x q - v q ≤ ∑ k ∈ Finset.univ.erase j, (x k - v k) :=
    Finset.single_le_sum (fun k hk => sub_nonneg.mpr (hle k (Finset.ne_of_mem_erase hk)))
      (by simp [hqj])
  have hvj := (hv.1 j).2
  rw [hvq] at hcoord
  linarith

lemma exchange_preserves (x v : Fin d → ℝ) (j p q : Fin d) (ε : ℝ)
    (hp : p ≠ j → x p ≠ v p) (hq : q ≠ j → x q ≠ v q) :
    Preserves v j x (exchange x p q ε) := by
  intro k hkj heq
  by_cases hkp : k = p
  · subst k
    exact False.elim (hp hkj heq)
  · by_cases hkq : k = q
    · subst k
      exact False.elim (hq hkj heq)
    · rw [exchange_elsewhere x p q k hkp hkq ε]
      exact heq
end HirschBoxSlice
end


-- BEGIN Solutions/BoxSlicePivot.lean
open Set Hirsch
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
namespace HirschBoxSlice
variable {d : ℕ}

lemma both_pivot (cap : Fin d → ℝ) (total : ℝ) (x v : Fin d → ℝ) (j p q : Fin d)
    (hx : x ∈ extremePoints ℝ (slice cap total))
    (ht : ∀ k, k ≠ j → AtBound cap v k)
    (hpq : p ≠ q) (hpj : p ≠ j) (hqj : q ≠ j)
    (hp : x p < v p) (hq : v q < x q)
    (hfixed : ∀ k, k ≠ p → k ≠ q → AtBound cap x k) :
    ∃ y, y ∈ extremePoints ℝ (slice cap total) ∧ Adj (slice cap total) x y ∧
      potential cap v j y < potential cap v j x := by
  have hvp := target_upper_of_inc cap total x v hx.1 (ht p hpj) hp
  have hvq := target_lower_of_dec cap total x v hx.1 (ht q hqj) hq
  have hpos : 0 < min (cap p - x p) (x q) := by
    apply lt_min
    · rw [← hvp]; exact sub_pos.mpr hp
    · rw [hvq] at hq; exact hq
  let ε := min (cap p - x p) (x q)
  let y := exchange x p q ε
  have hd : y ∈ extremePoints ℝ (slice cap total) ∧ Adj (slice cap total) x y ∧
      (y p = cap p ∨ y q = 0) :=
    maximal_exchange_vertex cap total x p q hpq hx.1 (regular_of_extreme cap total x hx) hfixed hpos
  rcases hd with ⟨hy, hedge, hfinish⟩
  have hpres : Preserves v j x y := exchange_preserves x v j p q ε
    (fun _ => ne_of_lt hp) (fun _ => ne_of_gt hq)
  have hhit : ∃ k, k ≠ j ∧ x k ≠ v k ∧ y k = v k := by
    rcases hfinish with hpf | hqf
    · exact ⟨p, hpj, ne_of_lt hp, hpf.trans hvp.symm⟩
    · exact ⟨q, hqj, ne_of_gt hq, hqf.trans hvq.symm⟩
  have hsigns := signs_preserved cap total x y v j hx.1 hy.1 ht hpres
  have hbuf : y j = x j := exchange_elsewhere x p q j hpj.symm hqj.symm ε
  have hm : Mixed cap v j y → Mixed cap v j x := by
    rintro ⟨hinside, hi, hd⟩
    refine ⟨?_, hsigns.1 hi, hsigns.2 hd⟩
    change 0 < y j ∧ y j < cap j at hinside
    change 0 < x j ∧ x j < cap j
    simpa only [hbuf] using hinside
  exact ⟨y, hy, hedge, potential_drop_hit hpres hhit hm⟩

lemma inc_buffer_pivot (cap : Fin d → ℝ) (total : ℝ) (x v : Fin d → ℝ) (j p : Fin d)
    (hx : x ∈ extremePoints ℝ (slice cap total)) (hv : v ∈ slice cap total)
    (ht : ∀ k, k ≠ j → AtBound cap v k)
    (hpj : p ≠ j) (hp : x p < v p)
    (hfixed : ∀ k, k ≠ p → k ≠ j → AtBound cap x k)
    (hcase : Mixed cap v j x ∨ ¬ Dec v j x) :
    ∃ y, y ∈ extremePoints ℝ (slice cap total) ∧ Adj (slice cap total) x y ∧
      potential cap v j y < potential cap v j x := by
  have hvp := target_upper_of_inc cap total x v hx.1 (ht p hpj) hp
  have hpRoom : 0 < cap p - x p := by rw [← hvp]; exact sub_pos.mpr hp
  have hjMass : 0 < x j := by
    rcases hcase with hm | hn
    · exact hm.1.1
    · exact lt_of_lt_of_le hpRoom (inc_buffer_capacity cap total x v j p hx.1 hv hpj hvp hn)
  have hpos : 0 < min (cap p - x p) (x j) := lt_min hpRoom hjMass
  let ε := min (cap p - x p) (x j)
  let y := exchange x p j ε
  have hd : y ∈ extremePoints ℝ (slice cap total) ∧ Adj (slice cap total) x y ∧
      (y p = cap p ∨ y j = 0) :=
    maximal_exchange_vertex cap total x p j hpj hx.1 (regular_of_extreme cap total x hx) hfixed hpos
  rcases hd with ⟨hy, hedge, hfinish⟩
  have hpres : Preserves v j x y := exchange_preserves x v j p j ε
    (fun _ => ne_of_lt hp) (fun h => False.elim (h rfl))
  refine ⟨y, hy, hedge, ?_⟩
  rcases hcase with hm | hn
  · rcases hfinish with hpf | hjf
    · have hhit : ∃ k, k ≠ j ∧ x k ≠ v k ∧ y k = v k :=
        ⟨p, hpj, ne_of_lt hp, hpf.trans hvp.symm⟩
      exact potential_drop_hit hpres hhit (fun _ => hm)
    · apply potential_drop_break hpres hm
      intro hym
      have h0 : 0 < y j := hym.1.1
      rw [hjf] at h0
      exact (lt_irrefl 0) h0
  · have hcap := inc_buffer_capacity cap total x v j p hx.1 hv hpj hvp hn
    have hpf : y p = v p := by
      rw [show y p = x p + ε from exchange_at_p x p j hpj ε]
      dsimp [ε]
      rw [min_eq_left hcap]
      linarith
    have hsigns := signs_preserved cap total x y v j hx.1 hy.1 ht hpres
    have hnot : ¬ Mixed cap v j y := fun hym => hn (hsigns.2 hym.2.2)
    exact potential_drop_hit hpres ⟨p, hpj, ne_of_lt hp, hpf⟩
      (fun hym => False.elim (hnot hym))

lemma dec_buffer_pivot (cap : Fin d → ℝ) (total : ℝ) (x v : Fin d → ℝ) (j q : Fin d)
    (hx : x ∈ extremePoints ℝ (slice cap total)) (hv : v ∈ slice cap total)
    (ht : ∀ k, k ≠ j → AtBound cap v k)
    (hqj : q ≠ j) (hq : v q < x q)
    (hfixed : ∀ k, k ≠ j → k ≠ q → AtBound cap x k)
    (hcase : Mixed cap v j x ∨ ¬ Inc v j x) :
    ∃ y, y ∈ extremePoints ℝ (slice cap total) ∧ Adj (slice cap total) x y ∧
      potential cap v j y < potential cap v j x := by
  have hvq := target_lower_of_dec cap total x v hx.1 (ht q hqj) hq
  have hqMass : 0 < x q := by rw [hvq] at hq; exact hq
  have hjRoom : 0 < cap j - x j := by
    rcases hcase with hm | hn
    · exact sub_pos.mpr hm.1.2
    · exact lt_of_lt_of_le hqMass (dec_buffer_capacity cap total x v j q hx.1 hv hqj hvq hn)
  have hpos : 0 < min (cap j - x j) (x q) := lt_min hjRoom hqMass
  let ε := min (cap j - x j) (x q)
  let y := exchange x j q ε
  have hd : y ∈ extremePoints ℝ (slice cap total) ∧ Adj (slice cap total) x y ∧
      (y j = cap j ∨ y q = 0) :=
    maximal_exchange_vertex cap total x j q hqj.symm hx.1 (regular_of_extreme cap total x hx) hfixed hpos
  rcases hd with ⟨hy, hedge, hfinish⟩
  have hpres : Preserves v j x y := exchange_preserves x v j j q ε
    (fun h => False.elim (h rfl)) (fun _ => ne_of_gt hq)
  refine ⟨y, hy, hedge, ?_⟩
  rcases hcase with hm | hn
  · rcases hfinish with hjf | hqf
    · apply potential_drop_break hpres hm
      intro hym
      have h1 : y j < cap j := hym.1.2
      rw [hjf] at h1
      exact (lt_irrefl _) h1
    · have hhit : ∃ k, k ≠ j ∧ x k ≠ v k ∧ y k = v k :=
        ⟨q, hqj, ne_of_gt hq, hqf.trans hvq.symm⟩
      exact potential_drop_hit hpres hhit (fun _ => hm)
  · have hcap := dec_buffer_capacity cap total x v j q hx.1 hv hqj hvq hn
    have hqf : y q = v q := by
      rw [show y q = x q - ε from exchange_at_q x j q hqj.symm ε]
      dsimp [ε]
      rw [min_eq_right hcap]
      linarith
    have hsigns := signs_preserved cap total x y v j hx.1 hy.1 ht hpres
    have hnot : ¬ Mixed cap v j y := fun hym => hn (hsigns.1 hym.2.1)
    exact potential_drop_hit hpres ⟨q, hqj, ne_of_gt hq, hqf⟩
      (fun hym => False.elim (hnot hym))

/-- Concrete pivot existence: every nonterminal vertex has an actual edge
to an extreme point of strictly smaller mismatch-plus-mixed-buffer potential.
The target buffer coordinate may itself be at a bound. -/
theorem decreasing_pivot (cap : Fin d → ℝ) (total : ℝ) (v : Fin d → ℝ) (j : Fin d)
    (hv : v ∈ slice cap total) (ht : ∀ k, k ≠ j → AtBound cap v k)
    (x : Fin d → ℝ) (hx : x ∈ extremePoints ℝ (slice cap total)) (hne : x ≠ v) :
    ∃ y, y ∈ extremePoints ℝ (slice cap total) ∧ Adj (slice cap total) x y ∧
      potential cap v j y < potential cap v j x := by
  classical
  have hr := regular_of_extreme cap total x hx
  by_cases hi : Inc v j x
  · by_cases hd : Dec v j x
    · by_cases hj : Inside cap x j
      · obtain ⟨p, hpj, hp⟩ := hi
        have hfixed : ∀ k, k ≠ p → k ≠ j → AtBound cap x k := by
          intro k hkp hkj
          exact bounds_except_inside cap total x hx.1 hr j hj k hkj
        exact inc_buffer_pivot cap total x v j p hx hv ht hpj hp hfixed
          (Or.inl ⟨hj, ⟨p, hpj, hp⟩, hd⟩)
      · obtain ⟨p, q, hpq, hpj, hqj, hp, hq, hfixed⟩ :=
          select_both cap total x v j hx.1 hr ht (bound_of_not_inside cap total x hx.1 j hj) hi hd
        exact both_pivot cap total x v j p q hx ht hpq hpj hqj hp hq hfixed
    · obtain ⟨p, hpj, hp, hfixed⟩ := select_inc_buffer cap total x v j hx.1 hr ht hi hd
      exact inc_buffer_pivot cap total x v j p hx hv ht hpj hp hfixed (Or.inr hd)
  · by_cases hd : Dec v j x
    · obtain ⟨q, hqj, hq, hfixed⟩ := select_dec_buffer cap total x v j hx.1 hr ht hi hd
      exact dec_buffer_pivot cap total x v j q hx hv ht hqj hq hfixed (Or.inr hi)
    · exact False.elim (hne (eq_of_no_signs total cap x v j hx.1 hv hi hd))
end HirschBoxSlice
end


-- BEGIN Solutions/BoxSlicePotential.lean
set_option autoImplicit false
namespace HirschBoxSlice

/-- Strict descent supplies a padded walk of any budget above the potential. -/
theorem walk_of_strict_potential
    {E : Type*} (R : E → E → Prop) (S : E → Prop)
    (v : E) (Φ : E → ℕ)
    (hnext : ∀ x, S x → x ≠ v → ∃ y, S y ∧ R x y ∧ Φ y < Φ x) :
    ∀ n : ℕ, ∀ x, S x → Φ x ≤ n → ∃ w : ℕ → E,
      w 0 = x ∧ w n = v ∧
      ∀ k < n, w k = w (k + 1) ∨ R (w k) (w (k + 1)) := by
  classical
  intro n
  induction n with
  | zero =>
      intro x hx hbound
      have heq : x = v := by
        by_contra h
        obtain ⟨y, hy, hedge, hdrop⟩ := hnext x hx h
        omega
      exact ⟨fun _ => v, heq.symm, rfl, by omega⟩
  | succ n ih =>
      intro x hx hbound
      by_cases heq : x = v
      · exact ⟨fun _ => v, heq.symm, rfl, fun _ _ => Or.inl rfl⟩
      · obtain ⟨y, hy, hedge, hdrop⟩ := hnext x hx heq
        obtain ⟨w, hw0, hwn, hws⟩ := ih y hy (by omega)
        let w' : ℕ → E := fun k => match k with
          | 0 => x
          | k + 1 => w k
        refine ⟨w', rfl, hwn, ?_⟩
        intro k hk
        cases k with
        | zero => exact Or.inr (by simpa only [w', hw0] using hedge)
        | succ k => exact hws k (by omega)
end HirschBoxSlice

-- BEGIN Solutions/BoxSliceDiameter.lean
open Set Hirsch HirschBoxSlice
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section

namespace HirschBoxSlice
/-- A box intersected with one sum equality has graph diameter at most its
number of coordinates. Empty slices and zero-width coordinates are allowed. -/
theorem slice_diameter (d : ℕ) (cap : Fin d → ℝ) (total : ℝ) :
    DiamLE (slice cap total) d := by
  classical
  intro u hu v hv
  by_cases hd : d = 0
  · subst d
    have huv : u = v := Subsingleton.elim _ _
    exact ⟨fun _ => v, huv.symm, rfl, by omega⟩
  · have hdpos : 0 < d := Nat.pos_of_ne_zero hd
    have hj : ∃ j : Fin d, ∀ k, k ≠ j → AtBound cap v k := by
      by_cases hf : ∃ k, Inside cap v k
      · obtain ⟨j, hj⟩ := hf
        exact ⟨j, bounds_except_inside cap total v hv.1 (regular_of_extreme cap total v hv) j hj⟩
      · let j : Fin d := ⟨0, hdpos⟩
        refine ⟨j, ?_⟩
        intro k hkj
        exact bound_of_not_inside cap total v hv.1 k (fun hk => hf ⟨k, hk⟩)
    obtain ⟨j, ht⟩ := hj
    exact walk_of_strict_potential (Adj (slice cap total))
      (fun x => x ∈ extremePoints ℝ (slice cap total)) v (potential cap v j)
      (fun x hx hne => decreasing_pivot cap total v j hv.1 ht x hx hne)
      d u hu (potential_le_dim cap v u j)
end HirschBoxSlice

/-- Exact publication statement. This is a restricted family theorem, not
the unrestricted polynomial Hirsch conjecture. -/
theorem solution (d : ℕ) (cap : Fin d → ℝ) (total : ℝ) :
    DiamLE {x : Fin d → ℝ | (∀ k, 0 ≤ x k ∧ x k ≤ cap k) ∧ ∑ k, x k = total} d := by
  exact HirschBoxSlice.slice_diameter d cap total

end


#print axioms HirschBoxSlice.decreasing_pivot
#print axioms solution
