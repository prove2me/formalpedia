-- Prove2me | solution 1 for Hirsch.zonotope_selected_direction_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-20T12:32:09.077033+00:00
-- url     : https://prove2.me/submissions/93392a4b-67d9-432b-a8ca-eb57f6489164

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

namespace Hirsch.ZonotopeDirections

open Set ZonotopeWall

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

/-- Turn an arbitrary whole exposed segment into the coefficient support face.
This does not assume a supplied coordinate edge or a graph encoding. -/
lemma exposed_segment_objective {d m : ℕ} (w : Fin m → (Fin d → ℝ))
    (u v : Fin d → ℝ)
    (hex : IsExposed ℝ (body w) (segment ℝ u v)) :
    ∃ f : (Fin d → ℝ) →ₗ[ℝ] ℝ, face w f = segment ℝ u v := by
  obtain ⟨f, hface⟩ := hex ⟨u, left_mem_segment ℝ u v⟩
  let g : (Fin d → ℝ) →ₗ[ℝ] ℝ := f.toLinearMap
  have hc := member_face w g (fun i => pick (g (w i)))
    (fun _ => pick_bounds _) (fun _ _ => rfl)
  refine ⟨g, ?_⟩
  ext x
  rw [hface]
  constructor
  · rintro ⟨hx, hfx⟩
    refine ⟨hx, ?_⟩
    rintro y ⟨s, hs, rfl⟩
    change g (point w s) ≤ g x
    rw [hfx]
    exact point_bound w g s hs
  · rintro ⟨hx, hmax⟩
    refine ⟨hx, ?_⟩
    obtain ⟨s, hs, he⟩ := hx
    have hupper := point_bound w g s hs
    rw [he] at hupper
    have hlower := hmax _ hc.1
    change g (point w (fun i => pick (g (w i)))) ≤ g x at hlower
    rw [hc.2] at hlower
    exact le_antisymm hupper hlower

/-- Along a genuine exposed edge, two changing nonzero generator coefficients
must belong to one direction, even for nonunique coefficient representations. -/
theorem changed_indices_parallel {d m : ℕ} (w : Fin m → (Fin d → ℝ))
    (s t : Fin m → ℝ) (hs : ∀ i, 0 ≤ s i ∧ s i ≤ 1)
    (ht : ∀ i, 0 ≤ t i ∧ t i ≤ 1)
    (hne : point w s ≠ point w t)
    (hex : IsExposed ℝ (body w) (segment ℝ (point w s) (point w t)))
    (i j : Fin m) (hwj : w j ≠ 0) (hi : s i ≠ t i) (hj : s j ≠ t j) :
    ∃ c : ℝ, w i = c • w j := by
  obtain ⟨f, hface⟩ := exposed_segment_objective w (point w s) (point w t) hex
  have hsface : point w s ∈ face w f := hface.symm ▸ left_mem_segment ℝ _ _
  have htface : point w t ∈ face w f := hface.symm ▸ right_mem_segment ℝ _ _
  have hsf := (point_eq_cap_iff w f s hs).mp hsface.2
  have htf := (point_eq_cap_iff w f t ht).mp htface.2
  have hfi : f (w i) = 0 := by
    by_contra h
    exact hi ((hsf i h).trans (htf i h).symm)
  have hfj : f (w j) = 0 := by
    by_contra h
    exact hj ((hsf j h).trans (htf j h).symm)
  obtain ⟨k, hwk, hfk, hline⟩ := segment_forces_line w f _ _ hne hface
  obtain ⟨ci, hci⟩ := hline i hfi
  obtain ⟨cj, hcj⟩ := hline j hfj
  have hcj0 : cj ≠ 0 := by
    intro h
    rw [h, zero_smul] at hcj
    exact hwj hcj
  refine ⟨ci / cj, ?_⟩
  rw [hci, hcj, smul_smul, div_mul_cancel₀ ci hcj0]

lemma pick_opposite (a : ℝ) (ha : a ≠ 0) :
    pick a ≠ pick (-a) ∧ pick a + pick (-a) = 1 := by
  by_cases hp : 0 < a
  · have hn : ¬ 0 < -a := by linarith
    simp only [pick, if_pos hp, if_neg hn]
    norm_num
  · have hn : a < 0 := lt_of_le_of_ne (le_of_not_gt hp) ha
    have hn' : 0 < -a := by linarith
    simp only [pick, if_neg hp, if_pos hn']
    norm_num

/-- Different endpoint values require an actual adjacent change. -/
lemma exists_change (L : ℕ) (a : Fin (L+1) → ℝ)
    (hne : a 0 ≠ a (Fin.last L)) :
    ∃ i : Fin L, a i.castSucc ≠ a i.succ := by
  by_contra h
  have hall : ∀ i : Fin L, a i.castSucc = a i.succ := by
    intro i
    by_contra hi
    exact h ⟨i, hi⟩
  have hconst : ∀ i : Fin (L+1), a i = a 0 := by
    intro i
    induction i using Fin.induction with
    | zero => rfl
    | succ i ih => exact (hall i).symm.trans ih
  exact hne (hconst (Fin.last L)).symm

/-- A finite family of distinct nonzero directions requires distinct steps
between a constructed pair of opposite actual vertices. -/
theorem antipodal_direction_lower_bound {d m r : ℕ}
    (w : Fin m → (Fin d → ℝ)) (selected : Fin r → Fin m)
    (hnonzero : ∀ i, w (selected i) ≠ 0)
    (hseparate : ∀ i j : Fin r, ∀ c : ℝ,
      w (selected i) = c • w (selected j) → i = j) :
    ∃ u v : Fin d → ℝ,
      u ∈ (body w).extremePoints ℝ ∧ v ∈ (body w).extremePoints ℝ ∧
      u + v = ∑ i : Fin m, w i ∧
      ∀ L : ℕ, ∀ p : Fin (L+1) → (Fin d → ℝ),
        p 0 = u → p (Fin.last L) = v →
        (∀ i, p i ∈ body w) →
        (∀ i : Fin L, p i.castSucc ≠ p i.succ ∧
          IsExposed ℝ (body w) (segment ℝ (p i.castSucc) (p i.succ))) → r ≤ L := by
  classical
  let S : Finset (Fin d → ℝ) := (Finset.univ.image w).filter (fun x => x ≠ 0)
  obtain ⟨f, hregular⟩ := Module.exists_dual_forall_apply_ne_zero (K := ℝ)
    (fun x : S => x.val) (fun x => (Finset.mem_filter.mp x.property).2)
  have hf : ∀ i, w i ≠ 0 → f (w i) ≠ 0 := by
    intro i hi
    apply hregular ⟨w i, ?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩, hi⟩
  have hneg : ∀ i, w i ≠ 0 → (-f) (w i) ≠ 0 := by
    intro i hi
    change -f (w i) ≠ 0
    exact neg_ne_zero.mpr (hf i hi)
  obtain ⟨u, hu, huface⟩ := regular_face w f hf
  obtain ⟨v, hv, hvface⟩ := regular_face w (-f) hneg
  have hucap : u ∈ face w f := huface.symm ▸ Set.mem_singleton u
  have hvcap : v ∈ face w (-f) := hvface.symm ▸ Set.mem_singleton v
  have hucorner : point w (fun i => pick (f (w i))) = u := by
    simpa only [huface, Set.mem_singleton_iff] using
      member_face w f (fun i => pick (f (w i))) (fun _ => pick_bounds _) (fun _ _ => rfl)
  have hvcorner : point w (fun i => pick ((-f) (w i))) = v := by
    simpa only [hvface, Set.mem_singleton_iff] using
      member_face w (-f) (fun i => pick ((-f) (w i)))
        (fun _ => pick_bounds _) (fun _ _ => rfl)
  have hopposite : u + v = ∑ i : Fin m, w i := by
    rw [← hucorner, ← hvcorner]
    unfold point
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : w i = 0
    · simp only [hi, smul_zero, add_zero]
    · change pick (f (w i)) • w i + pick (-f (w i)) • w i = w i
      rw [← add_smul, (pick_opposite (f (w i)) (hf i hi)).2, one_smul]
  refine ⟨u, v, hu, hv, hopposite, ?_⟩
  intro L p hp0 hpL hmem hedge
  have hcoeff : ∀ i : Fin (L+1), ∃ s : Fin m → ℝ,
      (∀ j, 0 ≤ s j ∧ s j ≤ 1) ∧ point w s = p i := fun i => hmem i
  choose s hs hpoint using hcoeff
  have hfirstcap : f (point w (s 0)) = cap w f := by
    rw [hpoint 0, hp0]
    exact hucap.2
  have hlastcap : (-f) (point w (s (Fin.last L))) = cap w (-f) := by
    rw [hpoint (Fin.last L), hpL]
    exact hvcap.2
  have hfirst := (point_eq_cap_iff w f (s 0) (hs 0)).mp hfirstcap
  have hlast := (point_eq_cap_iff w (-f) (s (Fin.last L)) (hs (Fin.last L))).mp hlastcap
  have hdifferent : ∀ a : Fin r, s 0 (selected a) ≠ s (Fin.last L) (selected a) := by
    intro a
    rw [hfirst _ (hf _ (hnonzero a)), hlast _ (hneg _ (hnonzero a))]
    change pick (f (w (selected a))) ≠ pick (-f (w (selected a)))
    exact (pick_opposite _ (hf _ (hnonzero a))).1
  have hchanges : ∀ a : Fin r, ∃ i : Fin L,
      s i.castSucc (selected a) ≠ s i.succ (selected a) := by
    intro a
    exact exists_change L (fun i => s i (selected a)) (hdifferent a)
  choose step hstep using hchanges
  have hinjective : Function.Injective step := by
    intro a b hab
    have hb := hstep b
    rw [← hab] at hb
    have hne : point w (s (step a).castSucc) ≠ point w (s (step a).succ) := by
      rw [hpoint, hpoint]
      exact (hedge (step a)).1
    have hex : IsExposed ℝ (body w)
        (segment ℝ (point w (s (step a).castSucc)) (point w (s (step a).succ))) := by
      rw [hpoint, hpoint]
      exact (hedge (step a)).2
    obtain ⟨c, hc⟩ := changed_indices_parallel w _ _ (hs _) (hs _) hne hex
      (selected a) (selected b) (hnonzero b) (hstep a) hb
    exact hseparate a b c hc
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective step hinjective

end Hirsch.ZonotopeDirections

/-- Selected distinct directions impose a lower bound on every original-edge
walk between constructed opposite vertices, not just on a sweep algorithm. -/
theorem solution (d m r : ℕ) (w : Fin m → (Fin d → ℝ))
    (selected : Fin r → Fin m)
    (hnonzero : ∀ i, w (selected i) ≠ 0)
    (hseparate : ∀ i j : Fin r, ∀ c : ℝ,
      w (selected i) = c • w (selected j) → i = j) :
    let Z : Set (Fin d → ℝ) := {x | ∃ s : Fin m → ℝ,
      (∀ i, 0 ≤ s i ∧ s i ≤ 1) ∧ (∑ i : Fin m, s i • w i) = x}
    ∃ u v : Fin d → ℝ,
      u ∈ Z.extremePoints ℝ ∧ v ∈ Z.extremePoints ℝ ∧
      u + v = ∑ i : Fin m, w i ∧
      ∀ L : ℕ, ∀ p : Fin (L+1) → (Fin d → ℝ),
        p 0 = u → p (Fin.last L) = v →
        (∀ i, p i ∈ Z) →
        (∀ i : Fin L, p i.castSucc ≠ p i.succ ∧
          IsExposed ℝ Z (segment ℝ (p i.castSucc) (p i.succ))) → r ≤ L := by
  exact Hirsch.ZonotopeDirections.antipodal_direction_lower_bound w selected hnonzero hseparate

#print axioms Hirsch.ZonotopeDirections.exposed_segment_objective
#print axioms Hirsch.ZonotopeDirections.changed_indices_parallel
#print axioms Hirsch.ZonotopeDirections.exists_change
#print axioms Hirsch.ZonotopeDirections.antipodal_direction_lower_bound
#print axioms solution
