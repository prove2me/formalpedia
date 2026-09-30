-- Prove2me | solution 1 for Hirsch.box_diameter_le_dimension
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-11T06:22:09.747182+00:00
-- url     : https://prove2.me/submissions/b6ebd3b5-1ea9-4111-87e6-5dbff0ffe08f

import Definitions.Def_Hirsch_model

set_option autoImplicit false
set_option maxHeartbeats 4000000
open Set Hirsch

noncomputable section

variable {d : ℕ}

def box (cap : Fin d → ℝ) : Set (Fin d → ℝ) :=
  {x | ∀ k, 0 ≤ x k ∧ x k ≤ cap k}

theorem atBound_of_extreme (cap : Fin d → ℝ) {x : Fin d → ℝ}
    (hx : x ∈ extremePoints ℝ (box cap)) (k : Fin d) :
    x k = 0 ∨ x k = cap k := by
  have hxB : x ∈ box cap := extremePoints_subset hx
  by_cases h0 : x k = 0
  · exact Or.inl h0
  · by_cases hcap : x k = cap k
    · exact Or.inr hcap
    · have hpos : 0 < x k := lt_of_le_of_ne (hxB k).1 (Ne.symm h0)
      have hlt : x k < cap k := lt_of_le_of_ne (hxB k).2 hcap
      let ε : ℝ := min (x k) (cap k - x k)
      have hε : 0 < ε := lt_min hpos (sub_pos.mpr hlt)
      let y : Fin d → ℝ := fun i => if i = k then x k + ε else x i
      let z : Fin d → ℝ := fun i => if i = k then x k - ε else x i
      have hy : y ∈ box cap := by
        intro i
        by_cases hik : i = k
        · subst i
          simp [y]
          constructor <;> linarith [min_le_left (x k) (cap k - x k),
            min_le_right (x k) (cap k - x k)]
        · simpa [y, hik] using hxB i
      have hz : z ∈ box cap := by
        intro i
        by_cases hik : i = k
        · subst i
          simp [z]
          constructor <;> linarith [min_le_left (x k) (cap k - x k),
            min_le_right (x k) (cap k - x k), (hxB k).2]
        · simpa [z, hik] using hxB i
      have hop : x ∈ openSegment ℝ y z := by
        refine ⟨(1 / 2 : ℝ), (1 / 2 : ℝ), by norm_num, by norm_num, by norm_num, ?_⟩
        funext i
        change (1 / 2 : ℝ) * y i + (1 / 2 : ℝ) * z i = x i
        by_cases hik : i = k
        · subst i; simp [y, z]; ring
        · simp [y, z, hik]; ring
      have hyx : y = x := hx.2 hy hz hop
      have heq := congrFun hyx k
      simp [y] at heq
      linarith

theorem extreme_of_atBound (cap : Fin d → ℝ) {x : Fin d → ℝ}
    (hx : x ∈ box cap) (hbd : ∀ k, x k = 0 ∨ x k = cap k) :
    x ∈ extremePoints ℝ (box cap) := by
  refine ⟨hx, ?_⟩
  intro y hy z hz hop
  obtain ⟨α, β, hα, hβ, hαβ, hcombo⟩ := hop
  funext k
  have hc := congrFun hcombo k
  change α * y k + β * z k = x k at hc
  rcases hbd k with hx0 | hxc
  · rw [hx0] at hc ⊢
    by_contra hne
    have hpos : 0 < y k := lt_of_le_of_ne (hy k).1 (Ne.symm hne)
    have hp := mul_pos hα hpos
    linarith [mul_nonneg hβ.le (hz k).1]
  · rw [hxc] at hc ⊢
    by_contra hne
    have hlt : y k < cap k := lt_of_le_of_ne (hy k).2 hne
    have hp := mul_pos hα (sub_pos.mpr hlt)
    have hw : α * cap k + β * cap k = cap k := by rw [← add_mul, hαβ, one_mul]
    nlinarith [mul_nonneg hβ.le (sub_nonneg.mpr (hz k).2)]

def coordWalk (u v : Fin d → ℝ) (t : ℕ) : Fin d → ℝ :=
  fun i => if i.val < t then v i else u i

theorem coordWalk_zero (u v : Fin d → ℝ) : coordWalk u v 0 = u := by
  funext i
  simp [coordWalk]

theorem coordWalk_dim (u v : Fin d → ℝ) : coordWalk u v d = v := by
  funext i
  have : i.val < d := i.isLt
  simp [coordWalk, this]

theorem coordWalk_mem_box (cap : Fin d → ℝ) {u v : Fin d → ℝ}
    (hu : u ∈ box cap) (hv : v ∈ box cap) (t : ℕ) :
    coordWalk u v t ∈ box cap := by
  intro k
  by_cases hk : k.val < t
  · simpa [coordWalk, hk] using hv k
  · simpa [coordWalk, hk] using hu k

theorem coordWalk_atBound (cap : Fin d → ℝ) {u v : Fin d → ℝ}
    (hu : ∀ k, u k = 0 ∨ u k = cap k)
    (hv : ∀ k, v k = 0 ∨ v k = cap k) (t : ℕ) (k : Fin d) :
    coordWalk u v t k = 0 ∨ coordWalk u v t k = cap k := by
  by_cases hk : k.val < t
  · simpa [coordWalk, hk] using hv k
  · simpa [coordWalk, hk] using hu k

theorem adj_one_coord (cap : Fin d → ℝ) {x y : Fin d → ℝ} {j : Fin d}
    (hx : x ∈ extremePoints ℝ (box cap))
    (hyB : y ∈ box cap)
    (hbdy : ∀ k, y k = 0 ∨ y k = cap k)
    (hother : ∀ k, k ≠ j → x k = y k)
    (hdiff : x j ≠ y j) :
    Adj (box cap) x y := by
  have hxB : x ∈ box cap := extremePoints_subset hx
  have hbdx : ∀ k, x k = 0 ∨ x k = cap k := fun k => atBound_of_extreme cap hx k
  have hsegF :
      segment ℝ x y ⊆ {z | z ∈ box cap ∧ ∀ k, k ≠ j → z k = x k} ∧
      {z | z ∈ box cap ∧ ∀ k, k ≠ j → z k = x k} ⊆ segment ℝ x y := by
    constructor
    · intro z hz
      obtain ⟨α, β, hα, hβ, hαβ, rfl⟩ := hz
      refine ⟨?_, ?_⟩
      · intro k
        have : (α • x + β • y) k = α * x k + β * y k := by simp
        rw [this]
        constructor <;> nlinarith [(hxB k).1, (hxB k).2, (hyB k).1, (hyB k).2]
      · intro k hkj
        have : (α • x + β • y) k = α * x k + β * y k := by simp
        have heq : x k = y k := hother k hkj
        rw [this, heq, ← add_mul, hαβ, one_mul]
    · intro z hz
      have hzj0 := (hz.1 j).1
      have hzj1 := (hz.1 j).2
      have hends : (x j = 0 ∧ y j = cap j) ∨ (x j = cap j ∧ y j = 0) := by
        rcases hbdx j with hx0 | hx1 <;> rcases hbdy j with hy0 | hy1
        · exact (hdiff (hx0.trans hy0.symm)).elim
        · exact Or.inl ⟨hx0, hy1⟩
        · exact Or.inr ⟨hx1, hy0⟩
        · exact (hdiff (hx1.trans hy1.symm)).elim
      have hcappos : 0 < cap j := by
        rcases hends with ⟨hx0, hy1⟩ | ⟨hx1, hy0⟩
        · have hnn : (0 : ℝ) ≤ cap j := by
            simpa [hy1] using (hyB j).1
          have hne : (0 : ℝ) ≠ cap j := by
            simpa [hx0, hy1] using hdiff
          exact lt_of_le_of_ne hnn hne
        · have hnn : (0 : ℝ) ≤ cap j := by
            simpa [hx1] using (hxB j).1
          have hne : (0 : ℝ) ≠ cap j := by
            simpa [hx1, hy0] using hdiff.symm
          exact lt_of_le_of_ne hnn hne
      have hcap : cap j ≠ 0 := ne_of_gt hcappos
      rcases hends with ⟨hx0, hy1⟩ | ⟨hx1, hy0⟩
      · let θ : ℝ := z j / cap j
        have hθ0 : 0 ≤ θ := div_nonneg hzj0 (le_of_lt hcappos)
        have hθ1 : θ ≤ 1 := (div_le_one hcappos).2 (by simpa [hy1] using hzj1)
        refine ⟨1 - θ, θ, sub_nonneg.2 hθ1, hθ0, by ring, ?_⟩
        funext k
        by_cases hkj : k = j
        · subst k
          change (1 - θ) * x j + θ * y j = z j
          simp [θ, hx0, hy1, div_mul_cancel₀ _ hcap]
        · have heq := hother k hkj
          have zeq := hz.2 k hkj
          change (1 - θ) * x k + θ * y k = z k
          rw [← heq, zeq]
          ring
      · let θ : ℝ := z j / cap j
        have hθ0 : 0 ≤ θ := div_nonneg hzj0 (le_of_lt hcappos)
        have hθ1 : θ ≤ 1 := (div_le_one hcappos).2 (by simpa [hx1] using hzj1)
        refine ⟨θ, 1 - θ, hθ0, sub_nonneg.2 hθ1, by ring, ?_⟩
        funext k
        by_cases hkj : k = j
        · subst k
          change θ * x j + (1 - θ) * y j = z j
          simp [θ, hx1, hy0, div_mul_cancel₀ _ hcap]
        · have heq := hother k hkj
          have zeq := hz.2 k hkj
          change θ * x k + (1 - θ) * y k = z k
          rw [← heq, zeq]
          ring
  have hFext : IsExtreme ℝ (box cap) (segment ℝ x y) := by
    have hset :
        segment ℝ x y = {z | z ∈ box cap ∧ ∀ k, k ≠ j → z k = x k} :=
      Subset.antisymm hsegF.1 hsegF.2
    rw [hset]
    refine ⟨fun z hz => hz.1, ?_⟩
    intro p hp q hq z hz hzopen
    refine ⟨hp, ?_⟩
    intro k hkj
    obtain ⟨α, β, hα, hβ, hαβ, hcombo⟩ := hzopen
    have hc := congrFun hcombo k
    change α * p k + β * q k = z k at hc
    have hzk : z k = x k := hz.2 k hkj
    rw [hzk] at hc
    rcases hbdx k with hx0 | hxc
    · rw [hx0] at hc ⊢
      by_contra hne
      have hpos : 0 < p k := lt_of_le_of_ne (hp k).1 (Ne.symm hne)
      have hp' := mul_pos hα hpos
      linarith [mul_nonneg hβ.le (hq k).1]
    · rw [hxc] at hc ⊢
      by_contra hne
      have hlt : p k < cap k := lt_of_le_of_ne (hp k).2 hne
      have hp' := mul_pos hα (sub_pos.mpr hlt)
      have hw : α * cap k + β * cap k = cap k := by rw [← add_mul, hαβ, one_mul]
      nlinarith [mul_nonneg hβ.le (sub_nonneg.mpr (hq k).2)]
  have hne : x ≠ y := fun h => hdiff (by rw [h])
  exact ⟨hne, hFext⟩

theorem solution (d : ℕ) (cap : Fin d → ℝ) :
    DiamLE {x : Fin d → ℝ | ∀ k, 0 ≤ x k ∧ x k ≤ cap k} d := by
  classical
  change DiamLE (box cap) d
  intro u hu v hv
  have huB : u ∈ box cap := extremePoints_subset hu
  have hvB : v ∈ box cap := extremePoints_subset hv
  have hbdu : ∀ k, u k = 0 ∨ u k = cap k := fun k => atBound_of_extreme cap hu k
  have hbdv : ∀ k, v k = 0 ∨ v k = cap k := fun k => atBound_of_extreme cap hv k
  refine ⟨coordWalk u v, coordWalk_zero u v, coordWalk_dim u v, ?_⟩
  intro t ht
  have htF : t < d := ht
  let j : Fin d := ⟨t, htF⟩
  have hother : ∀ k : Fin d, k ≠ j →
      coordWalk u v t k = coordWalk u v (t + 1) k := by
    intro k hkj
    have : k.val ≠ t := by
      intro hkv
      apply hkj
      exact Fin.ext (by simp [j, hkv])
    have hiff : k.val < t ↔ k.val < t + 1 := by omega
    simp [coordWalk, hiff]
  have hxtj : coordWalk u v t j = u j := by
    have : ¬ (j.val < t) := by simp [j]
    simp [coordWalk, this]
  have hytj : coordWalk u v (t + 1) j = v j := by
    have : j.val < t + 1 := by simp [j]
    simp [coordWalk, this]
  by_cases hsame : u j = v j
  · left
    funext k
    by_cases hkj : k = j
    · subst k
      simp [hxtj, hytj, hsame]
    · exact hother k hkj
  · right
    refine adj_one_coord cap ?_ ?_ ?_ hother ?_
    · exact extreme_of_atBound cap
        (coordWalk_mem_box cap huB hvB t)
        (coordWalk_atBound cap hbdu hbdv t)
    · exact coordWalk_mem_box cap huB hvB (t + 1)
    · exact coordWalk_atBound cap hbdu hbdv (t + 1)
    · simpa [hxtj, hytj] using hsame

#print axioms solution
