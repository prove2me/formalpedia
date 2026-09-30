-- Prove2me | solution 1 for Hirsch.zero_one_polytope_diameter_le_dimension
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-11T05:52:42.457848+00:00
-- url     : https://prove2.me/submissions/19d31321-d143-4e3e-ada6-eae95bcc9bc6

import Theorems.Thm_Hirsch_larman_bound
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Bornology.Basic

set_option autoImplicit false
set_option maxHeartbeats 4000000
open scoped RealInnerProductSpace InnerProduct
open Set Hirsch

noncomputable section

open Classical

variable {d n : ℕ}

theorem diamLE_mono {E : Type*} [AddCommGroup E] [Module ℝ E]
    (P : Set E) {m L : ℕ} (h : m ≤ L) (hP : DiamLE P m) : DiamLE P L := by
  intro u hu v hv
  obtain ⟨w, hw0, hwm, hs⟩ := hP u hu v hv
  refine ⟨fun i => w (min i m), ?_, ?_, ?_⟩
  · simp [hw0]
  · simp [min_eq_right h, hwm]
  · intro i hi
    by_cases h1 : i + 1 ≤ m
    · have hi' : i < m := Nat.lt_of_succ_le h1
      have hmin_i : min i m = i := min_eq_left (Nat.le_of_lt hi')
      have hmin_i1 : min (i + 1) m = i + 1 := min_eq_left h1
      simpa [hmin_i, hmin_i1] using hs i hi'
    · have hmi : min i m = m := by omega
      have hmi1 : min (i + 1) m = m := by omega
      exact Or.inl (by simp [hmi, hmi1])

theorem diamLE_pad_walk {E : Type*} [AddCommGroup E] [Module ℝ E]
    {P : Set E} {m B : ℕ} (h : m ≤ B)
    {u v : E} (hP : ∃ w : ℕ → E, w 0 = u ∧ w m = v ∧
      ∀ j < m, w j = w (j + 1) ∨ Adj P (w j) (w (j + 1))) :
    ∃ w : ℕ → E, w 0 = u ∧ w B = v ∧
      ∀ j < B, w j = w (j + 1) ∨ Adj P (w j) (w (j + 1)) := by
  obtain ⟨w, hw0, hwm, hs⟩ := hP
  refine ⟨fun i => w (min i m), ?_, ?_, ?_⟩
  · simp [hw0]
  · simp [min_eq_right h, hwm]
  · intro i hi
    by_cases h1 : i + 1 ≤ m
    · have hi' : i < m := Nat.lt_of_succ_le h1
      have hmin_i : min i m = i := min_eq_left (Nat.le_of_lt hi')
      have hmin_i1 : min (i + 1) m = i + 1 := min_eq_left h1
      simpa [hmin_i, hmin_i1] using hs i hi'
    · have hmi : min i m = m := by omega
      have hmi1 : min (i + 1) m = m := by omega
      exact Or.inl (by simp [hmi, hmi1])

theorem hpoly_convex (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) :
    Convex ℝ (Hpoly a b) := by
  intro x hx y hy u v hu hv huv
  intro i
  have hinner :
      ⟪a i, u • x + v • y⟫ = u * ⟪a i, x⟫ + v * ⟪a i, y⟫ := by
    simp [inner_add_right, inner_smul_right]
  have : u * ⟪a i, x⟫ + v * ⟪a i, y⟫ ≤ u * b i + v * b i :=
    add_le_add (mul_le_mul_of_nonneg_left (hx i) hu)
      (mul_le_mul_of_nonneg_left (hy i) hv)
  have hsum : u * b i + v * b i = b i := by rw [← add_mul, huv, one_mul]
  simpa [hinner, hsum] using this

theorem hpoly_isClosed (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) :
    IsClosed (Hpoly a b) := by
  have heq : Hpoly a b = ⋂ i : Fin n, {x | ⟪a i, x⟫ ≤ b i} := by
    ext x
    simp [Hpoly]
  rw [heq]
  exact isClosed_iInter fun i =>
    isClosed_le (innerSL ℝ (a i)).continuous continuous_const

theorem hpoly_isCompact_of_bounded
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hbd : Bornology.IsBounded (Hpoly a b)) :
    IsCompact (Hpoly a b) := by
  have hcl := hpoly_isClosed a b
  simpa [hcl.closure_eq] using hbd.isCompact_closure

theorem coord_continuous (i : Fin d) :
    Continuous fun x : EuclideanSpace ℝ (Fin d) => x i := by
  have hfun :
      (fun x : EuclideanSpace ℝ (Fin d) => x i) =
        fun x => ⟪EuclideanSpace.single i (1 : ℝ), x⟫ := by
    funext x
    simpa [EuclideanSpace.inner_single_left]
  rw [hfun]
  exact (innerSL ℝ (EuclideanSpace.single i (1 : ℝ))).continuous

theorem unit_cube_closed :
    IsClosed {x : EuclideanSpace ℝ (Fin d) | ∀ i : Fin d, 0 ≤ x i ∧ x i ≤ 1} := by
  have heq :
      {x : EuclideanSpace ℝ (Fin d) | ∀ i : Fin d, 0 ≤ x i ∧ x i ≤ 1} =
        ⋂ i : Fin d, {x | 0 ≤ x i ∧ x i ≤ 1} := by
    ext x
    simp [mem_iInter]
  rw [heq]
  refine isClosed_iInter fun i =>
    ((isClosed_le continuous_const (coord_continuous i)).inter
      (isClosed_le (coord_continuous i) continuous_const))

theorem unit_cube_convex :
    Convex ℝ {x : EuclideanSpace ℝ (Fin d) | ∀ i : Fin d, 0 ≤ x i ∧ x i ≤ 1} := by
  intro x hx y hy u v hu hv huv i
  have hz : (u • x + v • y) i = u * x i + v * y i := by
    simp [PiLp.add_apply, PiLp.smul_apply]
  have hx0 := (hx i).1
  have hx1 := (hx i).2
  have hy0 := (hy i).1
  have hy1 := (hy i).2
  rw [hz]
  constructor
  · nlinarith
  · nlinarith

theorem hpoly_subset_unit_cube
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hbd : Bornology.IsBounded (Hpoly a b))
    (h01 : ∀ x ∈ extremePoints ℝ (Hpoly a b),
      ∀ i : Fin d, x i = 0 ∨ x i = 1) :
    Hpoly a b ⊆ {x | ∀ i : Fin d, 0 ≤ x i ∧ x i ≤ 1} := by
  have hcomp := hpoly_isCompact_of_bounded a b hbd
  have hconv := hpoly_convex a b
  have hKM := closure_convexHull_extremePoints hcomp hconv
  have hcube :
      convexHull ℝ (extremePoints ℝ (Hpoly a b)) ⊆
        {x | ∀ i : Fin d, 0 ≤ x i ∧ x i ≤ 1} := by
    refine convexHull_min ?_ unit_cube_convex
    intro x hx i
    rcases h01 x hx i with h0 | h1
    · rw [h0]; constructor <;> norm_num
    · rw [h1]; constructor <;> norm_num
  have hcl : closure (convexHull ℝ (extremePoints ℝ (Hpoly a b))) ⊆
      {x | ∀ i : Fin d, 0 ≤ x i ∧ x i ≤ 1} :=
    (IsClosed.closure_subset_iff unit_cube_closed).2 hcube
  simpa [hKM] using hcl

theorem coord_slice_le_one_isExtreme
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) (j : Fin d)
    (hvalid : ∀ x ∈ Hpoly a b, x j ≤ 1) :
    IsExtreme ℝ (Hpoly a b) {x | x ∈ Hpoly a b ∧ x j = 1} := by
  refine ⟨fun x hx => hx.1, ?_⟩
  intro p hp q hq z hz hzopen
  refine ⟨hp, ?_⟩
  obtain ⟨α, β, hα, hβ, hαβ, hzcomb⟩ := hzopen
  have hzj : z j = 1 := hz.2
  have hinner : z j = α * p j + β * q j := by
    rw [← hzcomb]
    simp [PiLp.add_apply, PiLp.smul_apply]
  have hp1 := hvalid p hp
  have hq1 := hvalid q hq
  have hαpos : 0 < α := hα
  have hβnn : 0 ≤ β := hβ.le
  by_contra hpne
  have hplt : p j < 1 := lt_of_le_of_ne hp1 hpne
  have h1 : α * p j < α * 1 := mul_lt_mul_of_pos_left hplt hαpos
  have h2 : β * q j ≤ β * 1 := mul_le_mul_of_nonneg_left hq1 hβnn
  have hb : α * 1 + β * 1 = 1 := by rw [← add_mul, hαβ, one_mul]
  linarith

theorem coord_slice_ge_zero_isExtreme
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) (j : Fin d)
    (hvalid : ∀ x ∈ Hpoly a b, 0 ≤ x j) :
    IsExtreme ℝ (Hpoly a b) {x | x ∈ Hpoly a b ∧ x j = 0} := by
  refine ⟨fun x hx => hx.1, ?_⟩
  intro p hp q hq z hz hzopen
  refine ⟨hp, ?_⟩
  obtain ⟨α, β, hα, hβ, hαβ, hzcomb⟩ := hzopen
  have hzj : z j = 0 := hz.2
  have hinner : z j = α * p j + β * q j := by
    rw [← hzcomb]
    simp [PiLp.add_apply, PiLp.smul_apply]
  have hp0 := hvalid p hp
  have hq0 := hvalid q hq
  have hαpos : 0 < α := hα
  have hβnn : 0 ≤ β := hβ.le
  by_contra hpne
  have hppos : 0 < p j := lt_of_le_of_ne hp0 (Ne.symm hpne)
  have hprod := mul_pos hαpos hppos
  linarith [mul_nonneg hβnn hq0]

theorem adj_of_extreme_face {E : Type*} [AddCommGroup E] [Module ℝ E]
    {P F : Set E} {u v : E}
    (hF : IsExtreme ℝ P F) (h : Adj F u v) : Adj P u v :=
  ⟨h.1, hF.trans h.2⟩

theorem mem_hpoly_append {m : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (c : Fin m → EuclideanSpace ℝ (Fin d)) (β : Fin m → ℝ)
    (x : EuclideanSpace ℝ (Fin d)) :
    x ∈ Hpoly (Fin.append a c) (Fin.append b β) ↔
      x ∈ Hpoly a b ∧ x ∈ Hpoly c β := by
  constructor
  · intro hx
    refine ⟨fun i => ?_, fun j => ?_⟩
    · simpa [Fin.append_left] using hx (Fin.castAdd m i)
    · simpa [Fin.append_right] using hx (Fin.natAdd n j)
  · intro hx i
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · simpa [Fin.append_left] using hx.1 i
    · simpa [Fin.append_right] using hx.2 j

def sliceNormals (j : Fin d) : Fin 2 → EuclideanSpace ℝ (Fin d) :=
  fun k => if k = 0 then EuclideanSpace.single j (1 : ℝ)
    else EuclideanSpace.single j (-1)

def sliceBounds (α : ℝ) : Fin 2 → ℝ :=
  fun k => if k = 0 then α else -α

theorem mem_slice_hpoly
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (j : Fin d) (α : ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    x ∈ Hpoly (Fin.append a (sliceNormals j)) (Fin.append b (sliceBounds α)) ↔
      x ∈ Hpoly a b ∧ x j = α := by
  rw [mem_hpoly_append]
  constructor
  · intro ⟨hxP, hxS⟩
    refine ⟨hxP, ?_⟩
    have h0 := hxS (0 : Fin 2)
    have h1 := hxS (1 : Fin 2)
    have hine0 : ⟪EuclideanSpace.single j (1 : ℝ), x⟫ ≤ α := by
      simpa [sliceNormals, sliceBounds] using h0
    have hine1 : ⟪EuclideanSpace.single j (-1 : ℝ), x⟫ ≤ -α := by
      simpa [sliceNormals, sliceBounds] using h1
    have hxj : x j ≤ α := by
      simpa [EuclideanSpace.inner_single_left] using hine0
    have hαx : α ≤ x j := by
      have : -x j ≤ -α := by
        simpa [EuclideanSpace.inner_single_left] using hine1
      linarith
    linarith
  · intro ⟨hxP, hxj⟩
    refine ⟨hxP, ?_⟩
    intro k
    fin_cases k
    · simp [sliceNormals, sliceBounds, EuclideanSpace.inner_single_left, hxj]
    · simp [sliceNormals, sliceBounds, EuclideanSpace.inner_single_left, hxj]

noncomputable def varyingCoords
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) : Finset (Fin d) :=
  Finset.univ.filter (fun i =>
    ∃ u ∈ extremePoints ℝ (Hpoly a b),
      ∃ v ∈ extremePoints ℝ (Hpoly a b), u i ≠ v i)

theorem extreme_of_adj {E : Type*} [AddCommGroup E] [Module ℝ E]
    {P : Set E} {u v : E} (h : Adj P u v) :
    u ∈ extremePoints ℝ P := by
  have hseg : IsExtreme ℝ P (segment ℝ u v) := h.2
  have huP : u ∈ P := hseg.1 (left_mem_segment ℝ u v)
  refine mem_extremePoints_iff_left.2 ⟨huP, ?_⟩
  intro x1 hx1 x2 hx2 hop
  have hx1s : x1 ∈ segment ℝ u v :=
    hseg.left_mem_of_mem_openSegment hx1 hx2 (left_mem_segment ℝ u v) hop
  have hx2s : x2 ∈ segment ℝ u v :=
    hseg.right_mem_of_mem_openSegment hx1 hx2 (left_mem_segment ℝ u v) hop
  rw [segment_eq_image ℝ u v] at hx1s hx2s
  obtain ⟨s, ⟨hs0, hs1⟩, rfl⟩ := hx1s
  obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ := hx2s
  obtain ⟨a, b, ha, hb, hab, hcomb⟩ := hop
  have hexp :
      a • ((1 - s) • u + s • v) + b • ((1 - t) • u + t • v) =
        (a * (1 - s) + b * (1 - t)) • u + (a * s + b * t) • v := by
    simp [smul_add, smul_smul, add_smul]
    abel
  rw [hexp] at hcomb
  have hcu : a * (1 - s) + b * (1 - t) = 1 - (a * s + b * t) := by
    calc
      a * (1 - s) + b * (1 - t) = a + b - (a * s + b * t) := by ring
      _ = 1 - (a * s + b * t) := by rw [hab]
  rw [hcu] at hcomb
  set c := a * s + b * t
  have : c • (v - u) = 0 := by
    have hlin : (1 - c) • u + c • v = u := hcomb
    have : u + c • (v - u) = u := by
      calc
        u + c • (v - u) = u + (c • v - c • u) := by simp [smul_sub]
        _ = (u - c • u) + c • v := by abel
        _ = (1 - c) • u + c • v := by rw [sub_smul, one_smul]
        _ = u := hlin
    exact (add_eq_left.mp this)
  have hc0 : c = 0 := by
    by_contra hcne
    have : v - u = 0 := (smul_eq_zero.mp this).resolve_left hcne
    exact h.1 (eq_of_sub_eq_zero this).symm
  have hs00 : s = 0 := by
    have : a * s = 0 := by
      have has : 0 ≤ a * s := mul_nonneg ha.le hs0
      have hbt : 0 ≤ b * t := mul_nonneg hb.le ht0
      have hcdef : c = a * s + b * t := rfl
      nlinarith
    exact (mul_eq_zero.mp this).resolve_left ha.ne'
  subst s
  simp

theorem walk_stationary_eq {E : Type*} (w : ℕ → E) (B : ℕ)
    (h : ∀ i < B, w i = w (i + 1)) : ∀ i ≤ B, w i = w 0 := by
  intro i hi
  induction i with
  | zero => rfl
  | succ i ih =>
    have hi' : i < B := Nat.lt_of_succ_le hi
    exact (h i hi').symm.trans (ih (Nat.le_of_lt hi'))

theorem exists_first_change {E : Type*} (w : ℕ → E) (B : ℕ)
    (h : w 0 ≠ w B) :
    ∃ i < B, w i ≠ w (i + 1) ∧ ∀ j < i, w j = w (j + 1) := by
  classical
  have hex : ∃ i, i < B ∧ w i ≠ w (i + 1) := by
    by_contra hnone
    push_neg at hnone
    exact h ((walk_stationary_eq w B hnone B le_rfl).symm)
  let i := Nat.find hex
  have hi : i < B ∧ w i ≠ w (i + 1) := Nat.find_spec hex
  refine ⟨i, hi.1, hi.2, ?_⟩
  intro j hj
  have : ¬(j < B ∧ w j ≠ w (j + 1)) := Nat.find_min hex hj
  push_neg at this
  exact this (lt_trans hj hi.1)

theorem first_change_from_start {E : Type*} (w : ℕ → E) (B : ℕ)
    (h : w 0 ≠ w B) :
    ∃ x, ∃ i < B, w i = w 0 ∧ w (i + 1) = x ∧ w i ≠ x := by
  obtain ⟨i, hi, hne, hprev⟩ := exists_first_change w B h
  have hw0 : w i = w 0 := walk_stationary_eq w i hprev i le_rfl
  exact ⟨w (i + 1), i, hi, hw0, rfl, by simpa [hw0] using hne⟩

theorem diam_le_of_varying (N : ℕ) :
    ∀ (d n : ℕ) (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ),
      Bornology.IsBounded (Hpoly a b) →
      (∀ x ∈ extremePoints ℝ (Hpoly a b),
        ∀ i : Fin d, x i = 0 ∨ x i = 1) →
      (varyingCoords a b).card = N →
      DiamLE (Hpoly a b) N := by
  refine Nat.strong_induction_on N (fun N IH d n a b hbd h01 hN => ?_)
  intro u hu v hv
  classical
  let P := Hpoly a b
  have hcube := hpoly_subset_unit_cube a b hbd h01
  have huP : u ∈ P := extremePoints_subset hu
  have hvP : v ∈ P := extremePoints_subset hv
  by_cases huv : u = v
  · refine ⟨fun _ => u, rfl, huv, ?_⟩
    intro i hi
    exact Or.inl rfl
  have hNpos : 0 < N := by
    refine Nat.pos_of_ne_zero ?_
    intro h0
    have hcard : (varyingCoords a b).card = 0 := by simpa [h0] using hN
    have hempty : varyingCoords a b = ∅ := Finset.card_eq_zero.mp hcard
    apply huv
    refine (PiLp.ext ?_)
    intro i
    have : i ∉ varyingCoords a b := by simp [hempty]
    have hfilt : ¬(∃ u ∈ extremePoints ℝ P, ∃ v ∈ extremePoints ℝ P, u i ≠ v i) := by
      simpa [varyingCoords, P, Finset.mem_filter] using this
    push_neg at hfilt
    exact hfilt u hu v hv
  by_cases hshare : ∃ j ∈ varyingCoords a b, u j = v j
  · obtain ⟨j, hjvar, hjeq⟩ := hshare
    have hj01 : u j = 0 ∨ u j = 1 := h01 u hu j
    let α : ℝ := u j
    let aF := Fin.append a (sliceNormals j)
    let bF := Fin.append b (sliceBounds α)
    have hFset :
        Hpoly aF bF = {x | x ∈ P ∧ x j = α} := by
      ext x
      simpa [aF, bF, P] using mem_slice_hpoly a b j α x
    have hFsub : Hpoly aF bF ⊆ P := by
      intro x hx
      have hx' : x ∈ P ∧ x j = α := by simpa [hFset] using hx
      exact hx'.1
    have hbdF : Bornology.IsBounded (Hpoly aF bF) := hbd.subset hFsub
    have hFext : IsExtreme ℝ P (Hpoly aF bF) := by
      have hset : Hpoly aF bF = {x | x ∈ P ∧ x j = α} := hFset
      rcases hj01 with h0 | h1
      · have hα : α = 0 := h0
        have hvalid : ∀ x ∈ P, 0 ≤ x j := fun x hx => (hcube hx j).1
        have hE := coord_slice_ge_zero_isExtreme a b j hvalid
        simpa [hset, hα, P] using hE
      · have hα : α = 1 := h1
        have hvalid : ∀ x ∈ P, x j ≤ 1 := fun x hx => (hcube hx j).2
        have hE := coord_slice_le_one_isExtreme a b j hvalid
        simpa [hset, hα, P] using hE
    have h01F : ∀ x ∈ extremePoints ℝ (Hpoly aF bF),
        ∀ i : Fin d, x i = 0 ∨ x i = 1 := by
      intro x hx i
      exact h01 x (hFext.extremePoints_subset_extremePoints hx) i
    have huF : u ∈ Hpoly aF bF := by
      rw [hFset]; exact ⟨huP, rfl⟩
    have hvF : v ∈ Hpoly aF bF := by
      rw [hFset]; exact ⟨hvP, hjeq.symm ▸ rfl⟩
    have huExtF : u ∈ extremePoints ℝ (Hpoly aF bF) := by
      rw [hFext.extremePoints_eq]
      exact ⟨huF, hu⟩
    have hvExtF : v ∈ extremePoints ℝ (Hpoly aF bF) := by
      rw [hFext.extremePoints_eq]
      exact ⟨hvF, hv⟩
    have hvarF : varyingCoords aF bF ⊆ (varyingCoords a b).erase j := by
      intro k hk
      have hkex : ∃ u ∈ extremePoints ℝ (Hpoly aF bF),
          ∃ v ∈ extremePoints ℝ (Hpoly aF bF), u k ≠ v k := by
        simpa [varyingCoords, Finset.mem_filter] using hk
      obtain ⟨p, hp, q, hq, hpq⟩ := hkex
      have hpP : p ∈ extremePoints ℝ P :=
        hFext.extremePoints_subset_extremePoints hp
      have hqP : q ∈ extremePoints ℝ P :=
        hFext.extremePoints_subset_extremePoints hq
      have hkvar : k ∈ varyingCoords a b := by
        simp [varyingCoords, P, Finset.mem_filter]
        exact ⟨p, hpP, q, hqP, hpq⟩
      have hpj : p j = α := by
        have : p ∈ Hpoly aF bF := extremePoints_subset hp
        have : p ∈ P ∧ p j = α := by simpa [hFset] using this
        exact this.2
      have hqj : q j = α := by
        have : q ∈ Hpoly aF bF := extremePoints_subset hq
        have : q ∈ P ∧ q j = α := by simpa [hFset] using this
        exact this.2
      have hkj : k ≠ j := by
        intro hkj
        apply hpq
        simpa [hkj, hpj, hqj]
      exact Finset.mem_erase.2 ⟨hkj, hkvar⟩
    have hcardF : (varyingCoords aF bF).card < N := by
      have : (varyingCoords aF bF).card ≤ ((varyingCoords a b).erase j).card :=
        Finset.card_le_card hvarF
      have herase : ((varyingCoords a b).erase j).card =
          (varyingCoords a b).card - 1 := Finset.card_erase_of_mem hjvar
      have : (varyingCoords aF bF).card ≤ N - 1 := by
        simpa [herase, hN] using this
      exact lt_of_le_of_lt this (Nat.sub_one_lt_of_lt hNpos)
    obtain ⟨w, hw0, hwN, hs⟩ :=
      IH (varyingCoords aF bF).card hcardF d (n + 2) aF bF hbdF h01F rfl
        u huExtF v hvExtF
    refine diamLE_pad_walk (Nat.le_of_lt hcardF) ?_
    refine ⟨w, hw0, hwN, ?_⟩
    intro i hi
    rcases hs i hi with hstat | hadj
    · exact Or.inl hstat
    · exact Or.inr (adj_of_extreme_face hFext hadj)
  · -- No shared varying coordinate: a Larman walk supplies an incident edge,
    -- whose other end shares a varying coordinate with `u`.
    push_neg at hshare
    have hneP : P.Nonempty := ⟨u, huP⟩
    obtain ⟨wL, hwL0, hwLB, hsL⟩ :=
      larman_bound d n a b hneP hbd v hv u hu
    have hvne : wL 0 ≠ wL (n * 2 ^ (d - 3)) := by
      simpa [hwL0, hwLB] using (Ne.symm huv)
    obtain ⟨v', i, hi, hstart, hnext, hne⟩ :=
      first_change_from_start wL (n * 2 ^ (d - 3)) hvne
    have hadj : Adj P (wL i) (wL (i + 1)) := by
      rcases hsL i hi with hstat | hadj
      · exact (hne (hnext ▸ hstat)).elim
      · exact hadj
    have hv' : Adj P v v' := by
      simpa [hstart, hwL0, hnext] using hadj
    have hadj' : Adj P v' v :=
      ⟨hv'.1.symm, by simpa [segment_symm] using hv'.2⟩
    have hv'ext : v' ∈ extremePoints ℝ P := extreme_of_adj hadj'
    have h01v' : ∀ i : Fin d, v' i = 0 ∨ v' i = 1 := h01 v' hv'ext
    have hexk : ∃ k : Fin d, v' k ≠ v k := by
      have : v' ≠ v := hv'.1.symm
      contrapose! this
      exact PiLp.ext this
    obtain ⟨k, hkdiff⟩ := hexk
    have hkvar : k ∈ varyingCoords a b := by
      simp [varyingCoords, P, Finset.mem_filter]
      exact ⟨v', hv'ext, v, hv, hkdiff⟩
    have huk : u k ≠ v k := hshare k hkvar
    have hshare' : u k = v' k := by
      rcases h01 u hu k with hu0 | hu1
      · rcases h01 v hv k with hv0 | hv1
        · exact (huk (by simp [hu0, hv0])).elim
        · rcases h01v' k with hv'0 | hv'1
          · simpa [hu0] using hv'0.symm
          · exact (hkdiff (by simp [hv'1, hv1])).elim
      · rcases h01 v hv k with hv0 | hv1
        · rcases h01v' k with hv'0 | hv'1
          · exact (hkdiff (by simp [hv'0, hv0])).elim
          · simpa [hu1] using hv'1.symm
        · exact (huk (by simp [hu1, hv1])).elim
    -- Recurse on the face through coordinate `k` joining `u` and `v'`.
    have hj01 : u k = 0 ∨ u k = 1 := h01 u hu k
    let α : ℝ := u k
    let aF := Fin.append a (sliceNormals k)
    let bF := Fin.append b (sliceBounds α)
    have hFset :
        Hpoly aF bF = {x | x ∈ P ∧ x k = α} := by
      ext x
      simpa [aF, bF, P] using mem_slice_hpoly a b k α x
    have hFsub : Hpoly aF bF ⊆ P := by
      intro x hx
      have hx' : x ∈ P ∧ x k = α := by simpa [hFset] using hx
      exact hx'.1
    have hbdF : Bornology.IsBounded (Hpoly aF bF) := hbd.subset hFsub
    have hFext : IsExtreme ℝ P (Hpoly aF bF) := by
      have hset : Hpoly aF bF = {x | x ∈ P ∧ x k = α} := hFset
      rcases hj01 with h0 | h1
      · have hα : α = 0 := h0
        have hvalid : ∀ x ∈ P, 0 ≤ x k := fun x hx => (hcube hx k).1
        have hE := coord_slice_ge_zero_isExtreme a b k hvalid
        simpa [hset, hα, P] using hE
      · have hα : α = 1 := h1
        have hvalid : ∀ x ∈ P, x k ≤ 1 := fun x hx => (hcube hx k).2
        have hE := coord_slice_le_one_isExtreme a b k hvalid
        simpa [hset, hα, P] using hE
    have h01F : ∀ x ∈ extremePoints ℝ (Hpoly aF bF),
        ∀ i : Fin d, x i = 0 ∨ x i = 1 := by
      intro x hx i
      exact h01 x (hFext.extremePoints_subset_extremePoints hx) i
    have huF : u ∈ Hpoly aF bF := by
      rw [hFset]; exact ⟨huP, rfl⟩
    have hv'F : v' ∈ Hpoly aF bF := by
      rw [hFset]
      refine ⟨extremePoints_subset hv'ext, ?_⟩
      simpa [α] using hshare'.symm
    have huExtF : u ∈ extremePoints ℝ (Hpoly aF bF) := by
      rw [hFext.extremePoints_eq]
      exact ⟨huF, hu⟩
    have hv'ExtF : v' ∈ extremePoints ℝ (Hpoly aF bF) := by
      rw [hFext.extremePoints_eq]
      exact ⟨hv'F, hv'ext⟩
    have hvarF : varyingCoords aF bF ⊆ (varyingCoords a b).erase k := by
      intro i hi
      have hkex : ∃ p ∈ extremePoints ℝ (Hpoly aF bF),
          ∃ q ∈ extremePoints ℝ (Hpoly aF bF), p i ≠ q i := by
        simpa [varyingCoords, Finset.mem_filter] using hi
      obtain ⟨p, hp, q, hq, hpq⟩ := hkex
      have hpP : p ∈ extremePoints ℝ P :=
        hFext.extremePoints_subset_extremePoints hp
      have hqP : q ∈ extremePoints ℝ P :=
        hFext.extremePoints_subset_extremePoints hq
      have hivar : i ∈ varyingCoords a b := by
        simp [varyingCoords, P, Finset.mem_filter]
        exact ⟨p, hpP, q, hqP, hpq⟩
      have hpj : p k = α := by
        have : p ∈ Hpoly aF bF := extremePoints_subset hp
        have : p ∈ P ∧ p k = α := by simpa [hFset] using this
        exact this.2
      have hqj : q k = α := by
        have : q ∈ Hpoly aF bF := extremePoints_subset hq
        have : q ∈ P ∧ q k = α := by simpa [hFset] using this
        exact this.2
      have hik : i ≠ k := by
        intro hik
        apply hpq
        simpa [hik, hpj, hqj]
      exact Finset.mem_erase.2 ⟨hik, hivar⟩
    have hcardF : (varyingCoords aF bF).card < N := by
      have : (varyingCoords aF bF).card ≤ ((varyingCoords a b).erase k).card :=
        Finset.card_le_card hvarF
      have herase : ((varyingCoords a b).erase k).card =
          (varyingCoords a b).card - 1 := Finset.card_erase_of_mem hkvar
      have : (varyingCoords aF bF).card ≤ N - 1 := by
        simpa [herase, hN] using this
      exact lt_of_le_of_lt this (Nat.sub_one_lt_of_lt hNpos)
    obtain ⟨wF, hwF0, hwFN, hsF⟩ :=
      IH (varyingCoords aF bF).card hcardF d (n + 2) aF bF hbdF h01F rfl
        u huExtF v' hv'ExtF
    let M := (varyingCoords aF bF).card
    have hMle : M + 1 ≤ N := Nat.succ_le_of_lt hcardF
    -- Walk u --[M]--> v' --[1]--> v, then pad to N.
    let w : ℕ → EuclideanSpace ℝ (Fin d) := fun t =>
      if t ≤ M then wF t else v
    have hw0 : w 0 = u := by
      have : 0 ≤ M := Nat.zero_le _
      simp [w, hwF0, this]
    have hwEnd : w (M + 1) = v := by
      have : ¬ (M + 1 ≤ M) := by omega
      simp [w, this]
    have hsteps : ∀ t < M + 1,
        w t = w (t + 1) ∨ Adj P (w t) (w (t + 1)) := by
      intro t ht
      by_cases htM : t + 1 ≤ M
      · have ht' : t ≤ M := Nat.le_of_lt (Nat.lt_of_succ_le htM)
        have hwt : w t = wF t := if_pos ht'
        have hwt1 : w (t + 1) = wF (t + 1) := if_pos htM
        have htlt : t < M := Nat.lt_of_succ_le htM
        rcases hsF t htlt with hstat | hadj
        · exact Or.inl (by simp [hwt, hwt1, hstat])
        · exact Or.inr (by
            simpa [hwt, hwt1] using adj_of_extreme_face hFext hadj)
      · have htEq : t = M := by omega
        have hwt : w t = v' := by
          subst t
          have : M ≤ M := le_rfl
          simpa [w, this, hwFN]
        have hwt1 : w (t + 1) = v := by
          subst t
          have : ¬ (M + 1 ≤ M) := by omega
          simp [w, this]
        refine Or.inr ?_
        simpa [hwt, hwt1] using hadj'
    exact diamLE_pad_walk hMle ⟨w, hw0, hwEnd, hsteps⟩

theorem solution
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hbd : Bornology.IsBounded (Hpoly a b))
    (h01 : ∀ x ∈ extremePoints ℝ (Hpoly a b),
      ∀ i : Fin d, x i = 0 ∨ x i = 1) :
    DiamLE (Hpoly a b) d := by
  classical
  have hle : (varyingCoords a b).card ≤ d := by
    simpa using (varyingCoords a b).card_le_univ
  exact diamLE_mono (Hpoly a b) hle
    (diam_le_of_varying (varyingCoords a b).card d n a b hbd h01 rfl)

#print axioms solution
