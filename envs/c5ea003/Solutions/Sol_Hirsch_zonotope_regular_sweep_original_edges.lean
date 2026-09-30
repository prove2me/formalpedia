-- Prove2me | solution 1 for Hirsch.zonotope_regular_sweep_original_edges
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-19T18:36:54.06967+00:00
-- url     : https://prove2.me/submissions/b56d6fcd-3014-4068-8734-41611b8028ad

import Mathlib

open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section

namespace Hirsch.ZonotopeWall

open Set

def point {d m : ℕ} (w : Fin m → (Fin d → ℝ)) (t : Fin m → ℝ) : Fin d → ℝ :=
  ∑ i : Fin m, t i • w i

def body {d m : ℕ} (w : Fin m → (Fin d → ℝ)) : Set (Fin d → ℝ) :=
  {x | ∃ t : Fin m → ℝ, (∀ i, 0 ≤ t i ∧ t i ≤ 1) ∧ point w t = x}

def cap {d m : ℕ} (w : Fin m → (Fin d → ℝ)) (f : (Fin d → ℝ) →ₗ[ℝ] ℝ) : ℝ :=
  ∑ i : Fin m, max 0 (f (w i))

def pick (a : ℝ) : ℝ := if 0 < a then 1 else 0

def fixed {d m : ℕ} (w : Fin m → (Fin d → ℝ)) (f : (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (t : Fin m → ℝ) : Prop := ∀ i, f (w i) ≠ 0 → t i = pick (f (w i))

def face {d m : ℕ} (w : Fin m → (Fin d → ℝ)) (f : (Fin d → ℝ) →ₗ[ℝ] ℝ) :
    Set (Fin d → ℝ) := {x | x ∈ body w ∧ f x = cap w f}

lemma pick_bounds (a : ℝ) : 0 ≤ pick a ∧ pick a ≤ 1 := by
  unfold pick
  split_ifs <;> norm_num

lemma term_bound (a t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1) : t*a ≤ max 0 a := by
  by_cases ha : 0 ≤ a
  · rw [max_eq_right ha]
    exact (mul_le_mul_of_nonneg_right ht.2 ha).trans_eq (one_mul a)
  · have hn : a < 0 := lt_of_not_ge ha
    rw [max_eq_left hn.le]
    exact mul_nonpos_of_nonneg_of_nonpos ht.1 hn.le

lemma point_bound {d m : ℕ} (w : Fin m → (Fin d → ℝ))
    (f : (Fin d → ℝ) →ₗ[ℝ] ℝ) (t : Fin m → ℝ)
    (ht : ∀ i, 0 ≤ t i ∧ t i ≤ 1) : f (point w t) ≤ cap w f := by
  simp only [point,cap,map_sum,map_smul,smul_eq_mul]
  exact Finset.sum_le_sum (fun i _ => term_bound (f (w i)) (t i) (ht i))

/-- Every maximizing representation fixes exactly the non-tied coordinates. -/
lemma point_eq_cap_iff {d m : ℕ} (w : Fin m → (Fin d → ℝ))
    (f : (Fin d → ℝ) →ₗ[ℝ] ℝ) (t : Fin m → ℝ)
    (ht : ∀ i, 0 ≤ t i ∧ t i ≤ 1) : f (point w t) = cap w f ↔ fixed w f t := by
  classical
  constructor
  · intro he
    have hsum : ∑ i : Fin m, (max 0 (f (w i))-t i*f (w i)) = 0 := by
      rw [Finset.sum_sub_distrib]
      have hh := he
      simp only [point,cap,map_sum,map_smul,smul_eq_mul] at hh
      linarith
    intro i hi
    have hnon : ∀ j : Fin m, 0 ≤ max 0 (f (w j))-t j*f (w j) :=
      fun j => sub_nonneg.mpr (term_bound (f (w j)) (t j) (ht j))
    have hle := Finset.single_le_sum (fun j _ => hnon j) (Finset.mem_univ i)
    rw [hsum] at hle
    have heq : t i*f (w i) = max 0 (f (w i)) := by linarith [hnon i]
    by_cases hp : 0 < f (w i)
    · rw [max_eq_right hp.le] at heq
      change t i = if 0 < f (w i) then 1 else 0
      rw [if_pos hp]
      apply mul_right_cancel₀ (ne_of_gt hp)
      simpa only [one_mul] using heq
    · have hn : f (w i) < 0 := lt_of_le_of_ne (le_of_not_gt hp) hi
      rw [max_eq_left hn.le] at heq
      change t i = if 0 < f (w i) then 1 else 0
      rw [if_neg hp]
      exact (mul_eq_zero.mp heq).resolve_right hi
  · intro hf
    simp only [point,cap,map_sum,map_smul,smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : f (w i) = 0
    · simp [hi]
    · rw [hf i hi]
      by_cases hp : 0 < f (w i)
      · simp only [pick,if_pos hp,one_mul,max_eq_right hp.le]
      · simp only [pick,if_neg hp,zero_mul,max_eq_left (le_of_not_gt hp)]

lemma member_face {d m : ℕ} (w : Fin m → (Fin d → ℝ))
    (f : (Fin d → ℝ) →ₗ[ℝ] ℝ) (t : Fin m → ℝ)
    (ht : ∀ i, 0 ≤ t i ∧ t i ≤ 1) (hf : fixed w f t) : point w t ∈ face w f :=
  ⟨⟨t,ht,rfl⟩,(point_eq_cap_iff w f t ht).mpr hf⟩

lemma exposed_face {d m : ℕ} (w : Fin m → (Fin d → ℝ))
    (f : (Fin d → ℝ) →ₗ[ℝ] ℝ) : IsExposed ℝ (body w) (face w f) := by
  let t : Fin m → ℝ := fun i => pick (f (w i))
  have hb := member_face w f t (fun i => pick_bounds _) (fun _ _ => rfl)
  intro _
  refine ⟨f.toContinuousLinearMap,?_⟩
  ext x
  constructor
  · rintro ⟨hx,hfx⟩
    refine ⟨hx,?_⟩
    rintro y ⟨s,hs,rfl⟩
    change f (point w s) ≤ f x
    rw [hfx]
    exact point_bound w f s hs
  · rintro ⟨hx,hmax⟩
    refine ⟨hx,?_⟩
    obtain ⟨s,hs,rfl⟩ := hx
    have hh := hmax (point w t) hb.1
    change f (point w t) ≤ f (point w s) at hh
    rw [hb.2] at hh
    exact le_antisymm (point_bound w f s hs) hh

-- These two proof bodies are reused from accepted #309.
private lemma segment_parameter {d : ℕ} (u v z : Fin d → ℝ)
    (hz : z ∈ segment ℝ u v) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ z = u + t • (v-u) := by
  obtain ⟨s,t,hs,ht,hst,he⟩ := hz
  refine ⟨t,ht,by linarith,?_⟩
  have hs' : s = 1-t := by linarith
  rw [← he,hs']
  module

private lemma line_injective {d : ℕ} (D : Fin d → ℝ) (hD : D ≠ 0) :
    Function.Injective (fun t : ℝ => t • D) := by
  have hex : ∃ i, D i ≠ 0 := by
    by_contra hn
    apply hD
    funext i
    by_contra hi
    exact hn ⟨i,hi⟩
  obtain ⟨i,hi⟩ := hex
  intro s t he
  have hh := congrFun he i
  change s * D i = t * D i at hh
  exact mul_right_cancel₀ hi hh

lemma left_extreme_segment {d : ℕ} (u v : Fin d → ℝ) (hne : u ≠ v) :
    u ∈ (segment ℝ u v).extremePoints ℝ := by
  refine ⟨left_mem_segment ℝ _ _,?_⟩
  intro x hx y hy hseg
  obtain ⟨a,ha0,ha1,hxa⟩ := segment_parameter u v x hx
  obtain ⟨b,hb0,hb1,hyb⟩ := segment_parameter u v y hy
  obtain ⟨s,t,hs,ht,hst,he⟩ := hseg
  have hs' : s = 1-t := by linarith
  have hline : u+(s*a+t*b) • (v-u) = u := by
    calc
      u+(s*a+t*b) • (v-u) = s • (u+a • (v-u))+t • (u+b • (v-u)) := by
        rw [hs']
        module
      _ = u := by rw [← hxa,← hyb]; exact he
  have hD : v-u ≠ 0 := fun h => hne (sub_eq_zero.mp h).symm
  have hh : (s*a+t*b) • (v-u) = (0 : ℝ) • (v-u) := by
    apply add_left_cancel (a := u)
    simpa only [zero_smul,add_zero] using hline
  have hzero := line_injective (v-u) hD hh
  have hpa := mul_nonneg hs.le ha0
  have hpb := mul_nonneg ht.le hb0
  have hsa : s*a = 0 := by linarith
  have ha : a = 0 := (mul_eq_zero.mp hsa).resolve_left (ne_of_gt hs)
  simpa only [ha,zero_smul,add_zero] using hxa

lemma endpoints_extreme {d m : ℕ} (w : Fin m → (Fin d → ℝ))
    (f : (Fin d → ℝ) →ₗ[ℝ] ℝ) (u v : Fin d → ℝ)
    (hne : u ≠ v) (he : face w f = segment ℝ u v) :
    u ∈ (body w).extremePoints ℝ ∧ v ∈ (body w).extremePoints ℝ := by
  have hx := exposed_face w f
  rw [he] at hx
  refine ⟨hx.isExtreme.extremePoints_subset_extremePoints (left_extreme_segment u v hne),?_⟩
  apply hx.isExtreme.extremePoints_subset_extremePoints
  rw [segment_symm]
  exact left_extreme_segment v u (Ne.symm hne)

def low (c : ℝ) : ℝ := if c < 0 then 1 else 0

def high (c : ℝ) : ℝ := if 0 < c then 1 else 0

lemma low_bounds (c : ℝ) : 0 ≤ low c ∧ low c ≤ 1 := by
  unfold low
  split_ifs <;> norm_num

lemma high_bounds (c : ℝ) : 0 ≤ high c ∧ high c ≤ 1 := by
  unfold high
  split_ifs <;> norm_num

lemma scalar_bounds (c t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1) :
    0 ≤ (t-low c)*c ∧ (t-low c)*c ≤ |c| := by
  obtain ⟨ht0,ht1⟩ := ht
  by_cases hc : c < 0
  · rw [low,if_pos hc,abs_of_neg hc]
    constructor
    · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr ht1) hc.le
    · have hp := mul_nonpos_of_nonneg_of_nonpos ht0 hc.le
      nlinarith
  · have hc0 : 0 ≤ c := le_of_not_gt hc
    rw [low,if_neg hc,abs_of_nonneg hc0,sub_zero]
    constructor
    · exact mul_nonneg ht0 hc0
    · calc
        t*c ≤ 1*c := mul_le_mul_of_nonneg_right ht1 hc0
        _ = c := one_mul c

lemma scalar_full (c : ℝ) : (high c-low c)*c = |c| := by
  rcases lt_trichotomy c 0 with hc | hc | hc
  · simp only [high,low,if_pos hc,if_neg (not_lt.mpr hc.le),abs_of_neg hc]
    ring
  · subst c
    simp [high,low]
  · simp only [high,low,if_pos hc,if_neg (not_lt.mpr hc.le),abs_of_pos hc]
    ring

/-- A one-dimensional tied-generator space gives the ENTIRE original face,
with explicit endpoints and a strictly positive total segment length. -/
theorem line_face {d m : ℕ} (w : Fin m → (Fin d → ℝ))
    (f : (Fin d → ℝ) →ₗ[ℝ] ℝ) (j : Fin m) (hwj : w j ≠ 0) (hfj : f (w j)=0)
    (hc : ∀ i, f (w i)=0 → ∃ c : ℝ, w i = c • w j) :
    ∃ u v : Fin d → ℝ, u ≠ v ∧ face w f = segment ℝ u v := by
  classical
  have hchoose : ∀ i, ∃ c : ℝ, f (w i)=0 → w i = c • w j := by
    intro i
    by_cases hi : f (w i)=0
    · obtain ⟨c,hc⟩ := hc i hi
      exact ⟨c,fun _ => hc⟩
    · exact ⟨0,fun h => False.elim (hi h)⟩
  choose c hrep using hchoose
  let l : Fin m → ℝ := fun i => if f (w i)=0 then low (c i) else pick (f (w i))
  let h : Fin m → ℝ := fun i => if f (w i)=0 then high (c i) else pick (f (w i))
  have hlb : ∀ i, 0 ≤ l i ∧ l i ≤ 1 := by
    intro i
    dsimp only [l]
    split_ifs
    · exact low_bounds _
    · exact pick_bounds _
  have hhb : ∀ i, 0 ≤ h i ∧ h i ≤ 1 := by
    intro i
    dsimp only [h]
    split_ifs
    · exact high_bounds _
    · exact pick_bounds _
  have hlf : fixed w f l := by intro i hi; simp only [l,if_neg hi]
  have hhf : fixed w f h := by intro i hi; simp only [h,if_neg hi]
  let mass : ℝ := ∑ i : Fin m, if f (w i)=0 then |c i| else 0
  have hmass : 0 < mass := by
    have hcj : c j ≠ 0 := by
      intro hz
      have he := hrep j hfj
      rw [hz,zero_smul] at he
      exact hwj he
    have hle := Finset.single_le_sum
      (s := Finset.univ) (f := fun i : Fin m => if f (w i)=0 then |c i| else 0)
      (fun i _ => by
        change 0 ≤ (if f (w i)=0 then |c i| else 0)
        split_ifs
        · exact abs_nonneg _
        · exact le_rfl) (Finset.mem_univ j)
    simp only [hfj,if_true] at hle
    exact (abs_pos.mpr hcj).trans_le hle
  have hdispl : ∀ t : Fin m → ℝ, fixed w f t →
      point w t-point w l =
        (∑ i : Fin m, if f (w i)=0 then (t i-low (c i))*c i else 0) • w j := by
    intro t ht
    rw [point,point,← Finset.sum_sub_distrib,Finset.sum_smul]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : f (w i)=0
    · simp only [if_pos hi,l]
      rw [hrep i hi]
      module
    · simp only [if_neg hi,l,ht i hi,sub_self,zero_smul]
  have hfull : point w h-point w l = mass • w j := by
    rw [hdispl h hhf]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : f (w i)=0
    · simp only [hi,if_true,h]
      exact scalar_full (c i)
    · simp only [hi,if_false]
  have hne : point w l ≠ point w h := by
    intro he
    rw [← he,sub_self] at hfull
    have hz : mass • w j = (0 : ℝ) • w j := by simpa only [zero_smul] using hfull.symm
    exact (ne_of_gt hmass) (line_injective (w j) hwj hz)
  refine ⟨point w l,point w h,hne,?_⟩
  have hlface := member_face w f l hlb hlf
  have hhface := member_face w f h hhb hhf
  ext x
  constructor
  · rintro ⟨⟨t,ht,rfl⟩,he⟩
    have htf := (point_eq_cap_iff w f t ht).mp he
    let a : ℝ := ∑ i : Fin m, if f (w i)=0 then (t i-low (c i))*c i else 0
    have ha0 : 0 ≤ a := by
      apply Finset.sum_nonneg
      intro i _
      split_ifs
      · exact (scalar_bounds (c i) (t i) (ht i)).1
      · exact le_rfl
    have ha1 : a ≤ mass := by
      apply Finset.sum_le_sum
      intro i _
      split_ifs
      · exact (scalar_bounds (c i) (t i) (ht i)).2
      · exact le_rfl
    have heq : point w t-point w l = a • w j := hdispl t htf
    have hxeq : point w t = point w l+a • w j := by rw [← heq]; abel
    have hveq : point w h = point w l+mass • w j := by rw [← hfull]; abel
    have hr0 : 0 ≤ a/mass := div_nonneg ha0 hmass.le
    have hr1 : a/mass ≤ 1 := (div_le_one hmass).mpr ha1
    have hmul : (a/mass)*mass = a := div_mul_cancel₀ a (ne_of_gt hmass)
    refine ⟨1-a/mass,a/mass,by linarith,hr0,by ring,?_⟩
    rw [hveq,hxeq]
    simp only [smul_add,smul_smul,hmul]
    module
  · intro hx
    obtain ⟨a,b,ha,hb,hab,he⟩ := hx
    let t : Fin m → ℝ := a • l+b • h
    have htb : ∀ i, 0 ≤ t i ∧ t i ≤ 1 := by
      intro i
      change 0 ≤ a*l i+b*h i ∧ a*l i+b*h i ≤ 1
      constructor
      · exact add_nonneg (mul_nonneg ha (hlb i).1) (mul_nonneg hb (hhb i).1)
      · calc
          a*l i+b*h i ≤ a*1+b*1 := add_le_add
            (mul_le_mul_of_nonneg_left (hlb i).2 ha)
            (mul_le_mul_of_nonneg_left (hhb i).2 hb)
          _ = 1 := by simpa only [mul_one] using hab
    have htf : fixed w f t := by
      intro i hi
      change a*l i+b*h i = pick (f (w i))
      rw [hlf i hi,hhf i hi,← add_mul,hab,one_mul]
    have hpt : point w t = x := by
      calc
        point w t = a • point w l+b • point w h := by
          simp only [point,t,Pi.add_apply,Pi.smul_apply,smul_eq_mul,add_smul,
            mul_smul,Finset.sum_add_distrib]
          exact congrArg₂ (fun x y : Fin d → ℝ => x+y)
            (Finset.smul_sum (r:=a) (s:=Finset.univ) (f:=fun i => l i • w i)).symm
            (Finset.smul_sum (r:=b) (s:=Finset.univ) (f:=fun i => h i • w i)).symm
        _ = x := he
    exact hpt ▸ member_face w f t htb htf

/-- All generators tied by the objective can be tested inside the actual
support face by changing one coefficient of a fixed maximizing corner. -/
lemma toggle_tied {d m : ℕ} (w : Fin m → (Fin d → ℝ))
    (f : (Fin d → ℝ) →ₗ[ℝ] ℝ) (i : Fin m) (hi : f (w i)=0) :
    let b := point w (fun k => pick (f (w k)))
    b ∈ face w f ∧ b+w i ∈ face w f := by
  classical
  let t : Fin m → ℝ := fun k => pick (f (w k))
  have ht : ∀ k, 0 ≤ t k ∧ t k ≤ 1 := fun k => pick_bounds _
  have hti : t i=0 := by simp [t,pick,hi]
  have htnew : ∀ k, 0 ≤ Function.update t i 1 k ∧ Function.update t i 1 k ≤ 1 := by
    intro k
    by_cases hk : k=i
    · subst k
      simp only [Function.update_self]
      norm_num
    · simpa only [Function.update_of_ne hk] using ht k
  have hfnew : fixed w f (Function.update t i 1) := by
    intro k hk
    have hki : k ≠ i := by intro he; subst k; exact hk hi
    simp only [Function.update_of_ne hki,t]
  have hd : point w (Function.update t i 1)-point w t = w i := by
    unfold point
    rw [← Finset.sum_sub_distrib,Finset.sum_eq_single i]
    · simp only [Function.update_self,hti,one_smul,zero_smul,sub_zero]
    · intro k _ hki
      simp only [Function.update_of_ne hki,sub_self]
    · intro hnot
      exact False.elim (hnot (Finset.mem_univ i))
  have he : point w (Function.update t i 1) = point w t+w i := by rw [← hd]; abel
  exact ⟨member_face w f t ht (fun _ _ => rfl),
    he ▸ member_face w f (Function.update t i 1) htnew hfnew⟩

/-- Conversely, a whole nondegenerate support segment forces exactly one
nonzero generator direction among all objective ties. -/
theorem segment_forces_line {d m : ℕ} (w : Fin m → (Fin d → ℝ))
    (f : (Fin d → ℝ) →ₗ[ℝ] ℝ) (u v : Fin d → ℝ)
    (hne : u ≠ v) (he : face w f = segment ℝ u v) :
    ∃ j : Fin m, w j ≠ 0 ∧ f (w j)=0 ∧
      (∀ i, f (w i)=0 → ∃ c : ℝ, w i=c • w j) := by
  classical
  let t : Fin m → ℝ := fun i => pick (f (w i))
  let b := point w t
  have hb : b ∈ face w f := member_face w f t (fun _ => pick_bounds _) (fun _ _ => rfl)
  have hgen : ∃ j : Fin m, w j ≠ 0 ∧ f (w j)=0 := by
    by_contra hn
    have hall : ∀ i, f (w i)=0 → w i=0 := by
      intro i hi
      by_contra hwi
      exact hn ⟨i,hwi,hi⟩
    have hsingle : ∀ x ∈ face w f, x=b := by
      rintro x ⟨⟨s,hs,rfl⟩,hfs⟩
      have hfix := (point_eq_cap_iff w f s hs).mp hfs
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : f (w i)=0
      · simp only [hall i hi,smul_zero]
      · rw [hfix i hi]
    have hu := hsingle u (he.symm ▸ left_mem_segment ℝ u v)
    have hv := hsingle v (he.symm ▸ right_mem_segment ℝ u v)
    exact hne (hu.trans hv.symm)
  obtain ⟨j,hwj,hfj⟩ := hgen
  obtain ⟨a,_,_,hba⟩ := segment_parameter u v b (he ▸ hb)
  have hparallel : ∀ i, f (w i)=0 → ∃ c : ℝ, w i=c • (v-u) := by
    intro i hi
    have hbi := (toggle_tied w f i hi).2
    obtain ⟨r,_,_,hr⟩ := segment_parameter u v (b+w i) (he ▸ hbi)
    refine ⟨r-a,?_⟩
    calc
      w i = (b+w i)-b := by abel
      _ = (r-a) • (v-u) := by rw [hr,hba]; module
  obtain ⟨cj,hcj⟩ := hparallel j hfj
  have hcj0 : cj ≠ 0 := by
    intro hz
    rw [hz,zero_smul] at hcj
    exact hwj hcj
  refine ⟨j,hwj,hfj,?_⟩
  intro i hi
  obtain ⟨ci,hci⟩ := hparallel i hi
  refine ⟨ci/cj,?_⟩
  rw [hci,hcj,smul_smul,div_mul_cancel₀ ci hcj0]

end Hirsch.ZonotopeWall

namespace Hirsch.ZonotopeSweep

open Set ZonotopeWall

/-- Finite positive margins; the accepted finite-margin proof is reused. -/
lemma finite_margin {ι : Type*} (S : Finset ι) (a t : ι → ℝ)
    (ha : ∀ i ∈ S, 0 < a i) :
    ∃ e : ℝ, 0 < e ∧ ∀ i ∈ S, e * |t i| < a i := by
  classical
  revert ha
  induction S using Finset.induction_on with
  | empty =>
      intro ha
      exact ⟨1, by norm_num, by simp⟩
  | @insert i S hi ih =>
      intro ha
      obtain ⟨e, he, hS⟩ := ih (fun j hj => ha j (Finset.mem_insert_of_mem hj))
      have hai : 0 < a i := ha i (Finset.mem_insert_self i S)
      have hd : 0 < |t i| + 1 := by positivity
      let f : ℝ := a i / (|t i| + 1)
      have hf : 0 < f := div_pos hai hd
      have hfeq : f * (|t i| + 1) = a i := by
        dsimp [f]
        exact div_mul_cancel₀ _ (ne_of_gt hd)
      refine ⟨min e f, lt_min he hf, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with hji | hj
      · subst j
        have hb := mul_le_mul_of_nonneg_right (min_le_right e f) (abs_nonneg (t i))
        nlinarith
      · exact lt_of_le_of_lt
          (mul_le_mul_of_nonneg_right (min_le_left e f) (abs_nonneg (t j))) (hS j hj)

lemma small_shift (a b e : ℝ) (ha : a ≠ 0) (he : 0 < e)
    (hsmall : e * |b| < |a|) :
    a + e*b ≠ 0 ∧ (0 < a + e*b ↔ 0 < a) := by
  have hlo := mul_le_mul_of_nonneg_left (neg_abs_le b) he.le
  have hhi := mul_le_mul_of_nonneg_left (le_abs_self b) he.le
  by_cases hp : 0 < a
  · rw [abs_of_pos hp] at hsmall
    have hpos : 0 < a + e*b := by nlinarith
    exact ⟨ne_of_gt hpos, iff_of_true hpos hp⟩
  · have hn : a < 0 := lt_of_le_of_ne (le_of_not_gt hp) ha
    rw [abs_of_neg hn] at hsmall
    have hneg : a + e*b < 0 := by nlinarith
    exact ⟨ne_of_lt hneg, iff_of_false (not_lt.mpr hneg.le) hp⟩

/-- Resolve every nonzero vector in a finite test set, preserving every
already nonzero sign. The separating functional and perturbation are derived. -/
theorem regularize_on {d : ℕ} (S : Finset (Fin d → ℝ))
    (g : (Fin d → ℝ) →ₗ[ℝ] ℝ) :
    ∃ k : (Fin d → ℝ) →ₗ[ℝ] ℝ,
      (∀ v ∈ S, v ≠ 0 → k v ≠ 0) ∧
      ∀ v ∈ S, g v ≠ 0 → (0 < k v ↔ 0 < g v) := by
  classical
  let U := S.filter (fun v => v ≠ 0)
  obtain ⟨h, hh⟩ := Module.exists_dual_forall_apply_ne_zero (K := ℝ)
    (fun v : U => v.val) (fun v => (Finset.mem_filter.mp v.property).2)
  let J := U.filter (fun v => g v ≠ 0)
  have hpos : ∀ v ∈ J, 0 < |g v| := by
    intro v hv
    exact abs_pos.mpr (Finset.mem_filter.mp hv).2
  obtain ⟨e, he, hsmall⟩ := finite_margin J (fun v => |g v|) (fun v => h v) hpos
  let k : (Fin d → ℝ) →ₗ[ℝ] ℝ := g + e • h
  have hval : ∀ v, k v = g v + e * h v := by intro v; simp [k]
  have hkeep : ∀ v ∈ S, g v ≠ 0 → k v ≠ 0 ∧ (0 < k v ↔ 0 < g v) := by
    intro v hv hgv
    have hv0 : v ≠ 0 := by intro hzero; rw [hzero,map_zero] at hgv; exact hgv rfl
    have hvU : v ∈ U := Finset.mem_filter.mpr ⟨hv,hv0⟩
    have hvJ : v ∈ J := Finset.mem_filter.mpr ⟨hvU,hgv⟩
    rw [hval]
    exact small_shift (g v) (h v) e hgv he (hsmall v hvJ)
  refine ⟨k, ?_, fun v hv hg => (hkeep v hv hg).2⟩
  intro v hv hv0
  by_cases hgv : g v = 0
  · have hvU : v ∈ U := Finset.mem_filter.mpr ⟨hv,hv0⟩
    have hhv : h v ≠ 0 := hh ⟨v,hvU⟩
    rw [hval,hgv,zero_add]
    exact mul_ne_zero (ne_of_gt he) hhv
  · exact (hkeep v hv hgv).1

def blend {d : ℕ} (f k : (Fin d → ℝ) →ₗ[ℝ] ℝ) (t : ℝ) :
    (Fin d → ℝ) →ₗ[ℝ] ℝ := (1-t) • f + t • k

lemma blend_apply {d : ℕ} (f k : (Fin d → ℝ) →ₗ[ℝ] ℝ) (t : ℝ)
    (v : Fin d → ℝ) : blend f k t v = (1-t)*f v + t*k v := by simp [blend]

/-- A pair comparison detects exactly the dangerous simultaneous ties. -/
def contrast {d m : ℕ} (w : Fin m → (Fin d → ℝ))
    (f : (Fin d → ℝ) →ₗ[ℝ] ℝ) (i j : Fin m) : Fin d → ℝ :=
  f (w i) • w j - f (w j) • w i

lemma tied_contrast_zero {d m : ℕ} (w : Fin m → (Fin d → ℝ))
    (f k : (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (hsep : ∀ i j, contrast w f i j ≠ 0 → k (contrast w f i j) ≠ 0)
    (t : ℝ) (ht : 0 < t) (i j : Fin m)
    (hi : blend f k t (w i)=0) (hj : blend f k t (w j)=0) :
    contrast w f i j = 0 := by
  by_contra hn
  have hnon := hsep i j hn
  have hi' := hi
  have hj' := hj
  rw [blend_apply] at hi' hj'
  have hprod : t * (f (w i)*k (w j)-f (w j)*k (w i)) = 0 := by
    calc
      t * (f (w i)*k (w j)-f (w j)*k (w i)) =
        f (w i)*((1-t)*f (w j)+t*k (w j)) -
          f (w j)*((1-t)*f (w i)+t*k (w i)) := by ring
      _ = 0 := by rw [hi',hj']; ring
  have hzero := (mul_eq_zero.mp hprod).resolve_left (ne_of_gt ht)
  apply hnon
  simpa only [contrast,map_sub,map_smul,smul_eq_mul] using hzero

lemma tied_collinear {d m : ℕ} (w : Fin m → (Fin d → ℝ))
    (f k : (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (hf : ∀ i, w i ≠ 0 → f (w i) ≠ 0)
    (hsep : ∀ i j, contrast w f i j ≠ 0 → k (contrast w f i j) ≠ 0)
    (t : ℝ) (ht : 0 < t) (j : Fin m) (hwj : w j ≠ 0)
    (hj : blend f k t (w j)=0) :
    ∀ i, blend f k t (w i)=0 → ∃ c : ℝ, w i=c • w j := by
  intro i hi
  have hz := tied_contrast_zero w f k hsep t ht i j hi hj
  have heq : f (w j) • w i = f (w i) • w j := (sub_eq_zero.mp hz).symm
  have hfj := hf j hwj
  refine ⟨f (w i)/f (w j), ?_⟩
  calc
    w i = (f (w j))⁻¹ • (f (w j) • w i) := by
      rw [smul_smul,inv_mul_cancel₀ hfj,one_smul]
    _ = (f (w i)/f (w j)) • w j := by
      rw [heq,smul_smul]
      congr 1
      ring

noncomputable def crossingSet {d m : ℕ} (w : Fin m → (Fin d → ℝ))
    (f k : (Fin d → ℝ) →ₗ[ℝ] ℝ) : Finset ℝ := by
  classical
  exact (Finset.univ.image (fun i => f (w i)/(f (w i)-k (w i)))).filter
    (fun t => 0 < t ∧ t < 1 ∧ ∃ i, w i ≠ 0 ∧ blend f k t (w i)=0)

lemma crossing_card {d m : ℕ} (w : Fin m → (Fin d → ℝ))
    (f k : (Fin d → ℝ) →ₗ[ℝ] ℝ) : (crossingSet w f k).card ≤ m := by
  classical
  calc
    (crossingSet w f k).card ≤
        (Finset.univ.image (fun i => f (w i)/(f (w i)-k (w i)))).card :=
      Finset.card_filter_le _ _
    _ ≤ (Finset.univ : Finset (Fin m)).card := Finset.card_image_le
    _ = m := by simp

lemma mem_crossingSet {d m : ℕ} (w : Fin m → (Fin d → ℝ))
    (f k : (Fin d → ℝ) →ₗ[ℝ] ℝ) (hf : ∀ i, w i ≠ 0 → f (w i) ≠ 0)
    (t : ℝ) : t ∈ crossingSet w f k ↔
      0 < t ∧ t < 1 ∧ ∃ i, w i ≠ 0 ∧ blend f k t (w i)=0 := by
  classical
  constructor
  · intro ht
    exact (Finset.mem_filter.mp ht).2
  · rintro ⟨ht0,ht1,i,hwi,hi⟩
    have he := hi
    rw [blend_apply] at he
    have hden : f (w i)-k (w i) ≠ 0 := by
      intro hz
      have hh := sub_eq_zero.mp hz
      have hfi := hf i hwi
      apply hfi
      rw [← hh] at he
      nlinarith
    have hratio : t = f (w i)/(f (w i)-k (w i)) :=
      (eq_div_iff hden).mpr (by nlinarith [he])
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_image.mpr ⟨i,Finset.mem_univ i,hratio.symm⟩,ht0,ht1,i,hwi,hi⟩

/-- A regular objective exposes precisely one actual vertex, not a cube image
that might lie in the interior of the zonotope. -/
lemma regular_face {d m : ℕ} (w : Fin m → (Fin d → ℝ))
    (f : (Fin d → ℝ) →ₗ[ℝ] ℝ) (hf : ∀ i, w i ≠ 0 → f (w i) ≠ 0) :
    ∃ u ∈ (body w).extremePoints ℝ, face w f = {u} := by
  classical
  let t : Fin m → ℝ := fun i => pick (f (w i))
  let u := point w t
  have hu : u ∈ face w f := member_face w f t (fun _ => pick_bounds _) (fun _ _ => rfl)
  have heq : face w f = {u} := by
    ext x
    constructor
    · rintro ⟨⟨s,hs,rfl⟩,hfs⟩
      have hfix := (point_eq_cap_iff w f s hs).mp hfs
      change point w s = point w t
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : w i = 0
      · simp only [hi,smul_zero]
      · rw [hfix i (hf i hi)]
    · intro hx
      exact (Set.mem_singleton_iff.mp hx).symm ▸ hu
  have hex := exposed_face w f
  rw [heq] at hex
  exact ⟨u,hex.isExtreme.mem_extremePoints,heq⟩

lemma same_regular_face {d m : ℕ} (w : Fin m → (Fin d → ℝ))
    (f g : (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (hf : ∀ i, w i ≠ 0 → f (w i) ≠ 0)
    (hg : ∀ i, w i ≠ 0 → g (w i) ≠ 0)
    (hsign : ∀ i, 0 < f (w i) ↔ 0 < g (w i)) : face w f = face w g := by
  let t : Fin m → ℝ := fun i => pick (g (w i))
  have htf : fixed w f t := by
    intro i hi
    simp only [t,pick,hsign i]
  have htg : fixed w g t := fun _ _ => rfl
  have hbf := member_face w f t (fun _ => pick_bounds _) htf
  have hbg := member_face w g t (fun _ => pick_bounds _) htg
  obtain ⟨u,hu,heu⟩ := regular_face w f hf
  obtain ⟨v,hv,hev⟩ := regular_face w g hg
  have hbu : point w t=u := by simpa only [heu,Set.mem_singleton_iff] using hbf
  have hbv : point w t=v := by simpa only [hev,Set.mem_singleton_iff] using hbg
  rw [heu,hev,hbu.symm.trans hbv]

/-- Construct a straight objective sweep whose finite nonregular times all
expose genuine original edges; independent-direction coincidences are removed. -/
theorem regular_sweep {d m : ℕ} (w : Fin m → (Fin d → ℝ))
    (f g : (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (hf : ∀ i, w i ≠ 0 → f (w i) ≠ 0)
    (hg : ∀ i, w i ≠ 0 → g (w i) ≠ 0) :
    ∃ k : (Fin d → ℝ) →ₗ[ℝ] ℝ, ∃ T : Finset ℝ,
      (∀ i, (0 < k (w i) ↔ 0 < g (w i)) ∧ (w i ≠ 0 → k (w i) ≠ 0)) ∧
      face w k = face w g ∧ T.card ≤ m ∧
      (∀ t, t ∈ T ↔ 0 < t ∧ t < 1 ∧ ∃ i, w i ≠ 0 ∧ blend f k t (w i)=0) ∧
      (∀ t ∈ T, ∃ u v : Fin d → ℝ, u ≠ v ∧ face w (blend f k t)=segment ℝ u v ∧
        IsExposed ℝ (body w) (segment ℝ u v) ∧ IsExtreme ℝ (body w) (segment ℝ u v) ∧
        u ∈ (body w).extremePoints ℝ ∧ v ∈ (body w).extremePoints ℝ) ∧
      (∀ t, 0 ≤ t → t ≤ 1 → t ∉ T →
        ∃ u ∈ (body w).extremePoints ℝ, face w (blend f k t)={u}) := by
  classical
  let S : Finset (Fin d → ℝ) := Finset.univ.image w ∪
    Finset.univ.image (fun ij : Fin m × Fin m => contrast w f ij.1 ij.2)
  obtain ⟨k,hreg,hkeep⟩ := regularize_on S g
  have hwmem : ∀ i, w i ∈ S := fun i => Finset.mem_union_left _
    (Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩)
  have hsep : ∀ i j, contrast w f i j ≠ 0 → k (contrast w f i j) ≠ 0 := by
    intro i j hij
    apply hreg _ _ hij
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(i,j),Finset.mem_univ _,rfl⟩)
  have hk : ∀ i, w i ≠ 0 → k (w i) ≠ 0 := fun i hi => hreg _ (hwmem i) hi
  have hsign : ∀ i, 0 < k (w i) ↔ 0 < g (w i) := by
    intro i
    by_cases hi : w i=0
    · simp only [hi,map_zero]
    · exact hkeep _ (hwmem i) (hg i hi)
  refine ⟨k,crossingSet w f k,fun i => ⟨hsign i,hk i⟩,
    same_regular_face w k g hk hg hsign,crossing_card w f k,mem_crossingSet w f k hf,?_,?_⟩
  · intro t ht
    obtain ⟨ht0,ht1,j,hwj,hj⟩ := (mem_crossingSet w f k hf t).mp ht
    have hc := tied_collinear w f k hf hsep t ht0 j hwj hj
    obtain ⟨u,v,hne,heq⟩ := line_face w (blend f k t) j hwj hj hc
    have hex := exposed_face w (blend f k t)
    rw [heq] at hex
    have hep := endpoints_extreme w (blend f k t) u v hne heq
    exact ⟨u,v,hne,heq,hex,hex.isExtreme,hep.1,hep.2⟩
  · intro t ht0 ht1 hnot
    apply regular_face
    intro i hwi hi
    by_cases hz : t=0
    · subst t
      have hfi : f (w i)=0 := by simpa [blend] using hi
      exact hf i hwi hfi
    by_cases ho : t=1
    · subst t
      have hki : k (w i)=0 := by simpa [blend] using hi
      exact hk i hwi hki
    apply hnot
    apply (mem_crossingSet w f k hf t).mpr
    exact ⟨lt_of_le_of_ne ht0 (Ne.symm hz),lt_of_le_of_ne ht1 ho,i,hwi,hi⟩

end Hirsch.ZonotopeSweep

/-- A regularized straight sweep meets at most m exceptional objectives, and
all their whole support faces are original exposed edges. -/
theorem solution (d m : ℕ) (w : Fin m → (Fin d → ℝ))
    (f g : (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (hf : ∀ i, w i ≠ 0 → f (w i) ≠ 0)
    (hg : ∀ i, w i ≠ 0 → g (w i) ≠ 0) :
    let Z : Set (Fin d → ℝ) := {x | ∃ s : Fin m → ℝ,
      (∀ i, 0 ≤ s i ∧ s i ≤ 1) ∧ (∑ i : Fin m, s i • w i)=x}
    let F : ((Fin d → ℝ) →ₗ[ℝ] ℝ) → Set (Fin d → ℝ) :=
      fun h => {x | x ∈ Z ∧ h x = ∑ i : Fin m, max 0 (h (w i))}
    ∃ k : (Fin d → ℝ) →ₗ[ℝ] ℝ, ∃ T : Finset ℝ,
      (∀ i, (0 < k (w i) ↔ 0 < g (w i)) ∧ (w i ≠ 0 → k (w i) ≠ 0)) ∧
      F k = F g ∧ T.card ≤ m ∧
      (∀ t, t ∈ T ↔ 0 < t ∧ t < 1 ∧
        ∃ i, w i ≠ 0 ∧ ((1-t) • f + t • k) (w i)=0) ∧
      (∀ t ∈ T, ∃ u v : Fin d → ℝ, u ≠ v ∧ F ((1-t) • f + t • k)=segment ℝ u v ∧
        IsExposed ℝ Z (segment ℝ u v) ∧ IsExtreme ℝ Z (segment ℝ u v) ∧
        u ∈ Z.extremePoints ℝ ∧ v ∈ Z.extremePoints ℝ) ∧
      (∀ t, 0 ≤ t → t ≤ 1 → t ∉ T →
        ∃ u ∈ Z.extremePoints ℝ, F ((1-t) • f + t • k)={u}) := by
  exact Hirsch.ZonotopeSweep.regular_sweep w f g hf hg

#print axioms Hirsch.ZonotopeSweep.regularize_on
#print axioms Hirsch.ZonotopeSweep.tied_collinear
#print axioms Hirsch.ZonotopeSweep.mem_crossingSet
#print axioms Hirsch.ZonotopeSweep.regular_sweep
#print axioms solution
