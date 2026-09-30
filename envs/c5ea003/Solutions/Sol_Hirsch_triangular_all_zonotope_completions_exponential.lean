-- Prove2me | solution 1 for Hirsch.triangular_all_zonotope_completions_exponential
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-21T19:02:18.004781+00:00
-- url     : https://prove2.me/submissions/ea54d85a-0fa7-479f-973a-b7ba4059f215

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

end Hirsch.ZonotopeSweep

namespace Hirsch.CompletionDirections

open Set ZonotopeWall

/-- Remove the component along a given nonzero coordinate of D. -/
def transverseProjection {d : ℕ} (D : Fin d → ℝ) (j : Fin d) :
    (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ) where
  toFun x := x - (x j / D j) • D
  map_add' x y := by
    simp only [Pi.add_apply, add_div, add_smul]
    module
  map_smul' a x := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_div_assoc]
    module

lemma projection_self {d : ℕ} (D : Fin d → ℝ) (j : Fin d) (hj : D j ≠ 0) :
    transverseProjection D j D = 0 := by
  change D - (D j / D j) • D = 0
  rw [div_self hj, one_smul, sub_self]

lemma projection_kernel {d : ℕ} (D x : Fin d → ℝ) (j : Fin d)
    (hx : transverseProjection D j x = 0) : ∃ c : ℝ, x = c • D := by
  exact ⟨x j / D j, sub_eq_zero.mp hx⟩

/-- Every genuine exposed edge of a finite convex hull forces a parallel
nonzero generator in EVERY compact-summand zonotope completion. -/
theorem inherited_edge_direction {d m : ℕ} (C : Finset (Fin d → ℝ))
    (Q : Set (Fin d → ℝ)) (hQc : IsCompact Q) (hQne : Q.Nonempty)
    (w : Fin m → (Fin d → ℝ))
    (hZ : {z | ∃ x ∈ convexHull ℝ (C : Set (Fin d → ℝ)), ∃ y ∈ Q, x+y=z} = body w)
    (u v : Fin d → ℝ) (hu : u ∈ convexHull ℝ (C : Set (Fin d → ℝ)))
    (hv : v ∈ convexHull ℝ (C : Set (Fin d → ℝ))) (hne : u ≠ v)
    (hex : IsExposed ℝ (convexHull ℝ (C : Set (Fin d → ℝ))) (segment ℝ u v)) :
    ∃ i : Fin m, w i ≠ 0 ∧ ∃ c : ℝ, w i = c • (v-u) := by
  classical
  let P : Set (Fin d → ℝ) := convexHull ℝ (C : Set (Fin d → ℝ))
  let D := v-u
  have hD : D ≠ 0 := fun h => hne (sub_eq_zero.mp h).symm
  obtain ⟨j, hj⟩ : ∃ j : Fin d, D j ≠ 0 := by
    by_contra hn
    apply hD
    funext j
    by_contra hj
    exact hn ⟨j,hj⟩
  let π := transverseProjection D j
  have hπD : π D = 0 := projection_self D j hj
  obtain ⟨f, hface⟩ := hex ⟨u, left_mem_segment ℝ u v⟩
  let f₀ : (Fin d → ℝ) →ₗ[ℝ] ℝ := f.toLinearMap
  have huF : u ∈ P ∧ ∀ x ∈ P, f x ≤ f u := by
    change u ∈ {x ∈ P | ∀ y ∈ P, f y ≤ f x}
    rw [← hface]
    exact left_mem_segment ℝ u v
  have hvF : v ∈ P ∧ ∀ x ∈ P, f x ≤ f v := by
    change v ∈ {x ∈ P | ∀ y ∈ P, f y ≤ f x}
    rw [← hface]
    exact right_mem_segment ℝ u v
  have hfv : f₀ v = f₀ u := le_antisymm (huF.2 v hv) (hvF.2 u hu)
  have hfD : f₀ D = 0 := by
    change f₀ (v-u) = 0
    rw [map_sub, hfv, sub_self]
  have hfπ : ∀ x, f₀ (π x) = f₀ x := by
    intro x
    change f₀ (x-(x j/D j) • D) = f₀ x
    rw [map_sub, map_smul, smul_eq_mul, hfD, mul_zero, sub_zero]
  by_contra hmissing
  have hprojected : ∀ i, w i ≠ 0 → π (w i) ≠ 0 := by
    intro i hi hp
    apply hmissing
    exact ⟨i,hi,projection_kernel D (w i) j hp⟩
  let S : Finset (Fin d → ℝ) :=
    Finset.univ.image (fun i => π (w i)) ∪ C.image (fun x => π (u-x))
  obtain ⟨k, hk, hkeep⟩ := ZonotopeSweep.regularize_on S f₀
  let g : (Fin d → ℝ) →ₗ[ℝ] ℝ := k.comp π
  have hgD : g D = 0 := by
    change k (π D) = 0
    rw [hπD, map_zero]
  have hgv : g v = g u := by
    apply sub_eq_zero.mp
    rw [← map_sub]
    exact hgD
  have hgreg : ∀ i, w i ≠ 0 → g (w i) ≠ 0 := by
    intro i hi
    apply hk _ _ (hprojected i hi)
    exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩)
  have hCmax : ∀ x ∈ C, g x ≤ g u := by
    intro x hx
    by_cases hxs : x ∈ segment ℝ u v
    · obtain ⟨s,t,hs,ht,hst,he⟩ := hxs
      rw [← he, map_add, map_smul, map_smul, hgv]
      change s*g u+t*g u ≤ g u
      rw [← add_mul,hst,one_mul]
    · have hxP : x ∈ P := subset_convexHull ℝ _ hx
      have hfx : f₀ x < f₀ u := by
        apply lt_of_le_of_ne (huF.2 x hxP)
        intro he
        apply hxs
        rw [hface]
        refine ⟨hxP,?_⟩
        intro y hy
        exact (huF.2 y hy).trans_eq he.symm
      have hpos : 0 < f₀ (π (u-x)) := by
        rw [hfπ, map_sub]
        exact sub_pos.mpr hfx
      have hm : π (u-x) ∈ S :=
        Finset.mem_union_right _ (Finset.mem_image.mpr ⟨x,hx,rfl⟩)
      have hgpos : 0 < g (u-x) := (hkeep _ hm (ne_of_gt hpos)).mpr hpos
      rw [map_sub] at hgpos
      exact (sub_pos.mp hgpos).le
  have hhalf : Convex ℝ {x : Fin d → ℝ | g x ≤ g u} := by
    intro x hx y hy s t hs ht hst
    change g (s • x+t • y) ≤ g u
    simp only [map_add,map_smul,smul_eq_mul]
    calc
      s*g x+t*g y ≤ s*g u+t*g u := add_le_add
        (mul_le_mul_of_nonneg_left hx hs) (mul_le_mul_of_nonneg_left hy ht)
      _ = g u := by rw [← add_mul,hst,one_mul]
  have hPmax : ∀ x ∈ P, g x ≤ g u := by
    intro x hx
    exact (convexHull_min (show (C : Set (Fin d → ℝ)) ⊆ {y | g y ≤ g u}
      from fun y hy => hCmax y hy) hhalf) hx
  obtain ⟨q,hq,hqmax⟩ := hQc.exists_isMaxOn hQne g.toContinuousLinearMap.continuous.continuousOn
  have hqmax' : ∀ y ∈ Q, g y ≤ g q := hqmax
  have hzu : u+q ∈ body w := hZ ▸ (show u+q ∈
      {z | ∃ x ∈ P, ∃ y ∈ Q, x+y=z} from ⟨u,hu,q,hq,rfl⟩)
  have hzv : v+q ∈ body w := hZ ▸ (show v+q ∈
      {z | ∃ x ∈ P, ∃ y ∈ Q, x+y=z} from ⟨v,hv,q,hq,rfl⟩)
  have hsummax : ∀ z ∈ body w, g z ≤ g (u+q) := by
    intro z hz
    have hz' : z ∈ {z | ∃ x ∈ P, ∃ y ∈ Q, x+y=z} := hZ.symm ▸ hz
    obtain ⟨x,hx,y,hy,rfl⟩ := hz'
    rw [map_add,map_add]
    exact add_le_add (hPmax x hx) (hqmax' y hy)
  have hbodycap : ∀ z ∈ body w, g z ≤ cap w g := by
    rintro z ⟨s,hs,rfl⟩
    exact point_bound w g s hs
  have hcorner := member_face w g (fun i => pick (g (w i)))
    (fun _ => pick_bounds _) (fun _ _ => rfl)
  have hcaple : cap w g ≤ g (u+q) := by
    have h := hsummax _ hcorner.1
    rw [hcorner.2] at h
    exact h
  have hleft : u+q ∈ face w g := ⟨hzu,le_antisymm (hbodycap _ hzu) hcaple⟩
  have heval : g (v+q) = g (u+q) := by rw [map_add,map_add,hgv]
  have hright : v+q ∈ face w g := ⟨hzv,heval.trans hleft.2⟩
  obtain ⟨z,hz,hfacez⟩ := ZonotopeDirections.regular_face w g hgreg
  have hleftz : u+q=z := by simpa only [hfacez, Set.mem_singleton_iff] using hleft
  have hrightz : v+q=z := by simpa only [hfacez, Set.mem_singleton_iff] using hright
  exact hne (add_right_cancel (hleftz.trans hrightz.symm))

/-- A selected family of distinct summand edge directions injects into the
completion's generator directions and forces its intrinsic diameter lower bound. -/
theorem completion_lower_bound {d m r : ℕ} (C : Finset (Fin d → ℝ))
    (Q : Set (Fin d → ℝ)) (hQc : IsCompact Q) (hQne : Q.Nonempty)
    (w : Fin m → (Fin d → ℝ))
    (hZ : {z | ∃ x ∈ convexHull ℝ (C : Set (Fin d → ℝ)), ∃ y ∈ Q, x+y=z} = body w)
    (a b : Fin r → (Fin d → ℝ))
    (hedge : ∀ i, a i ∈ convexHull ℝ (C : Set (Fin d → ℝ)) ∧
      b i ∈ convexHull ℝ (C : Set (Fin d → ℝ)) ∧ a i ≠ b i ∧
      IsExposed ℝ (convexHull ℝ (C : Set (Fin d → ℝ))) (segment ℝ (a i) (b i)))
    (hdirections : ∀ i j : Fin r, ∀ c : ℝ, b i-a i = c • (b j-a j) → i=j) :
    (∃ selected : Fin r → Fin m, Function.Injective selected ∧
      ∀ i, w (selected i) ≠ 0 ∧ ∃ c : ℝ, w (selected i) = c • (b i-a i)) ∧
    r ≤ m ∧ ∃ u v : Fin d → ℝ,
      u ∈ (body w).extremePoints ℝ ∧ v ∈ (body w).extremePoints ℝ ∧
      u+v = ∑ i : Fin m, w i ∧
      ∀ L : ℕ, ∀ p : Fin (L+1) → (Fin d → ℝ),
        p 0=u → p (Fin.last L)=v → (∀ i, p i ∈ body w) →
        (∀ i : Fin L, p i.castSucc ≠ p i.succ ∧
          IsExposed ℝ (body w) (segment ℝ (p i.castSucc) (p i.succ))) → r ≤ L := by
  classical
  have hselect : ∀ i : Fin r, ∃ j : Fin m, w j ≠ 0 ∧ ∃ c : ℝ, w j=c • (b i-a i) := by
    intro i
    have h := hedge i
    exact inherited_edge_direction C Q hQc hQne w hZ (a i) (b i) h.1 h.2.1 h.2.2.1 h.2.2.2
  choose selected hnonzero c hc using hselect
  have hcne : ∀ i, c i ≠ 0 := by
    intro i hz
    have h := hc i
    rw [hz,zero_smul] at h
    exact hnonzero i h
  have hseparate : ∀ i j : Fin r, ∀ s : ℝ,
      w (selected i)=s • w (selected j) → i=j := by
    intro i j s he
    have hscaled : c i • (b i-a i) = (s*c j) • (b j-a j) := by
      simpa only [hc i,hc j,smul_smul] using he
    apply hdirections i j ((s*c j)/(c i))
    calc
      b i-a i = (c i)⁻¹ • (c i • (b i-a i)) := by
        rw [smul_smul,inv_mul_cancel₀ (hcne i),one_smul]
      _ = ((s*c j)/(c i)) • (b j-a j) := by
        rw [hscaled,smul_smul]
        congr 1
        ring
  have hinj : Function.Injective selected := by
    intro i j he
    apply hseparate i j 1
    rw [he,one_smul]
  have hcard : r ≤ m := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective selected hinj
  exact ⟨⟨selected,hinj,fun i => ⟨hnonzero i,c i,hc i⟩⟩,hcard,
    ZonotopeDirections.antipodal_direction_lower_bound w selected hnonzero hseparate⟩

end Hirsch.CompletionDirections

namespace TriangularFamily

def tail {n : ℕ} {α : Type*} (x : Fin (n+1) → α) : Fin n → α :=
  fun i => x i.succ

def lead : (n : ℕ) → (Fin n → ℝ) → ℝ
  | 0, _ => 0
  | _+1, x => x 0

def branch (e : ℝ) (b : Bool) (x : ℝ) : ℝ :=
  if b then 1-e*x else e*x

def level (e : ℝ) : (n : ℕ) → (Fin n → Bool) → ℝ
  | 0, _ => 0
  | n+1, b => branch e (b 0) (level e n (tail b))

def point (e : ℝ) : (n : ℕ) → (Fin n → Bool) → (Fin n → ℝ)
  | 0, _ => fun i => Fin.elim0 i
  | n+1, b => Fin.cons (level e (n+1) b) (point e n (tail b))

def Feasible (e : ℝ) {n : ℕ} (x : Fin n → ℝ) : Prop :=
  (∀ i, 0 ≤ x i ∧ x i ≤ 1) ∧
    ∀ (i j : Fin n), i.val+1 = j.val → e*x j ≤ x i ∧ x i ≤ 1-e*x j

private theorem branch_interval (e x : ℝ) (b : Bool)
    (he : 0 < e) (he2 : e < 1/2) (hx : 0 ≤ x ∧ x ≤ 1) :
    e*x ≤ branch e b x ∧ branch e b x ≤ 1-e*x := by
  have hle : e*x ≤ e := by nlinarith [mul_nonneg he.le (sub_nonneg.mpr hx.2)]
  cases b <;> simp [branch] <;> linarith

private theorem level_bounds (e : ℝ) (he : 0 < e) (he2 : e < 1/2) :
    ∀ n (b : Fin n → Bool), 0 ≤ level e n b ∧ level e n b ≤ 1 := by
  intro n
  induction n with
  | zero => intro b; simp [level]
  | succ n ih =>
    intro b
    have hb := ih (tail b)
    have hz := mul_nonneg he.le hb.1
    have hi := branch_interval e (level e n (tail b)) (b 0) he he2 hb
    change 0 ≤ branch e (b 0) (level e n (tail b)) ∧
      branch e (b 0) (level e n (tail b)) ≤ 1
    constructor <;> linarith

private theorem level_injective (e : ℝ) (he : 0 < e) (he2 : e < 1/2) :
    ∀ n, Function.Injective (level e n) := by
  intro n
  induction n with
  | zero =>
    intro a b _
    funext i
    exact Fin.elim0 i
  | succ n ih =>
    intro a b hab
    have ha := level_bounds e he he2 n (tail a)
    have hb := level_bounds e he he2 n (tail b)
    have hla : e*level e n (tail a) ≤ e :=
      (mul_le_mul_of_nonneg_left ha.2 he.le).trans_eq (mul_one e)
    have hlb : e*level e n (tail b) ≤ e :=
      (mul_le_mul_of_nonneg_left hb.2 he.le).trans_eq (mul_one e)
    have hhead : a 0 = b 0 := by
      cases h0 : a 0 <;> cases h1 : b 0
      · rfl
      · simp [level, branch, h0, h1] at hab
        linarith
      · simp [level, branch, h0, h1] at hab
        linarith
      · rfl
    have hprod : e*level e n (tail a) = e*level e n (tail b) := by
      change branch e (a 0) (level e n (tail a)) =
        branch e (b 0) (level e n (tail b)) at hab
      rw [hhead] at hab
      cases h0 : b 0 <;> simp [branch, h0, ne_of_gt he] at hab <;>
        exact congrArg (fun t : ℝ => e*t) hab
    have ht : tail a = tail b := ih (mul_left_cancel₀ (ne_of_gt he) hprod)
    funext i
    exact Fin.cases hhead (fun j => congrFun ht j) i

private theorem lead_point (e : ℝ) (n : ℕ) (b : Fin n → Bool) :
    lead n (point e n b) = level e n b := by
  cases n <;> rfl

private theorem point_injective (e : ℝ) (he : 0 < e) (he2 : e < 1/2)
    (n : ℕ) : Function.Injective (point e n) := by
  intro a b hab
  apply level_injective e he he2 n
  simpa only [lead_point] using congrArg (lead n) hab

private theorem tail_feasible {e : ℝ} {n : ℕ} {x : Fin (n+1) → ℝ}
    (hx : Feasible e x) : Feasible e (tail x) := by
  refine ⟨fun i => hx.1 i.succ, ?_⟩
  intro i j hij
  exact hx.2 i.succ j.succ (by simp only [Fin.val_succ]; omega)

private theorem head_interval {e : ℝ} {n : ℕ} {x : Fin (n+1) → ℝ}
    (hx : Feasible e x) :
    e*lead n (tail x) ≤ x 0 ∧ x 0 ≤ 1-e*lead n (tail x) := by
  cases n with
  | zero => simpa only [lead, mul_zero, sub_zero] using hx.1 0
  | succ n => exact hx.2 0 (0 : Fin (n+1)).succ (by rfl)

private theorem point_feasible (e : ℝ) (he : 0 < e) (he2 : e < 1/2) :
    ∀ n (b : Fin n → Bool), Feasible e (point e n b) := by
  intro n
  induction n with
  | zero =>
    intro b
    exact ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  | succ n ih =>
    intro b
    have ht := ih (tail b)
    constructor
    · intro i
      exact Fin.cases (level_bounds e he he2 (n+1) b) (fun j => ht.1 j) i
    · intro i j hij
      cases i using Fin.cases with
      | zero =>
        cases n with
        | zero => have hj := j.isLt; simp only [Fin.val_zero] at hij; omega
        | succ n =>
          have hj : j = (0 : Fin (n+1)).succ := by
            apply Fin.ext
            simpa only [Fin.val_zero, Fin.val_succ, zero_add] using hij.symm
          subst j
          exact branch_interval e (level e (n+1) (tail b)) (b 0) he he2
            (level_bounds e he he2 (n+1) (tail b))
      | succ i =>
        cases j using Fin.cases with
        | zero => simp only [Fin.val_zero, Fin.val_succ] at hij; omega
        | succ j => exact ht.2 i j (by simp only [Fin.val_succ] at hij; omega)

private theorem endpoint_combo (lo hi x y z a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hab : a+b=1)
    (hx : lo ≤ x ∧ x ≤ hi) (hy : lo ≤ y ∧ y ≤ hi)
    (hz : z=lo ∨ z=hi) (heq : a*x+b*y=z) : x=z ∧ y=z := by
  rcases hz with h | h
  · rw [h] at heq ⊢
    have h1 := mul_nonneg ha.le (sub_nonneg.mpr hx.1)
    have h2 := mul_nonneg hb.le (sub_nonneg.mpr hy.1)
    have hs : a*(x-lo)+b*(y-lo)=0 := by
      calc
        a*(x-lo)+b*(y-lo) = (a*x+b*y)-(a+b)*lo := by ring
        _ = 0 := by rw [heq, hab]; ring
    have hax : a*(x-lo)=0 := by linarith
    have hby : b*(y-lo)=0 := by linarith
    exact ⟨sub_eq_zero.mp ((mul_eq_zero.mp hax).resolve_left (ne_of_gt ha)),
      sub_eq_zero.mp ((mul_eq_zero.mp hby).resolve_left (ne_of_gt hb))⟩
  · rw [h] at heq ⊢
    have h1 := mul_nonneg ha.le (sub_nonneg.mpr hx.2)
    have h2 := mul_nonneg hb.le (sub_nonneg.mpr hy.2)
    have hs : a*(hi-x)+b*(hi-y)=0 := by
      calc
        a*(hi-x)+b*(hi-y) = (a+b)*hi-(a*x+b*y) := by ring
        _ = 0 := by rw [heq, hab]; ring
    have hax : a*(hi-x)=0 := by linarith
    have hby : b*(hi-y)=0 := by linarith
    exact ⟨(sub_eq_zero.mp ((mul_eq_zero.mp hax).resolve_left (ne_of_gt ha))).symm,
      (sub_eq_zero.mp ((mul_eq_zero.mp hby).resolve_left (ne_of_gt hb))).symm⟩

private theorem point_combo (e : ℝ) :
    ∀ n (bits : Fin n → Bool) (y z : Fin n → ℝ) (a b : ℝ),
      0 < a → 0 < b → a+b=1 → Feasible e y → Feasible e z →
      a • y + b • z = point e n bits →
      y = point e n bits ∧ z = point e n bits := by
  intro n
  induction n with
  | zero =>
    intro bits y z a b _ _ _ _ _ _
    constructor <;> funext i <;> exact Fin.elim0 i
  | succ n ih =>
    intro bits y z a b ha hb hab hy hz heq
    have htail : a • tail y + b • tail z = point e n (tail bits) := by
      funext i
      exact congrFun heq i.succ
    have ht := ih (tail bits) (tail y) (tail z) a b ha hb hab
      (tail_feasible hy) (tail_feasible hz) htail
    have hy0 := head_interval hy
    have hz0 := head_interval hz
    rw [ht.1] at hy0
    rw [ht.2] at hz0
    have hend : (point e (n+1) bits) 0 = e*lead n (point e n (tail bits)) ∨
        (point e (n+1) bits) 0 = 1-e*lead n (point e n (tail bits)) := by
      simp only [lead_point]
      change branch e (bits 0) (level e n (tail bits)) = e*level e n (tail bits) ∨
        branch e (bits 0) (level e n (tail bits)) = 1-e*level e n (tail bits)
      cases h : bits 0 <;> simp [branch, h]
    have h0 : a*y 0+b*z 0 = (point e (n+1) bits) 0 := congrFun heq 0
    have hh := endpoint_combo _ _ _ _ _ _ _ ha hb hab hy0 hz0 hend h0
    constructor
    · funext i
      exact Fin.cases hh.1 (fun j => congrFun ht.1 j) i
    · funext i
      exact Fin.cases hh.2 (fun j => congrFun ht.2 j) i

private theorem point_extreme (e : ℝ) (he : 0 < e) (he2 : e < 1/2)
    (n : ℕ) (bits : Fin n → Bool) :
    point e n bits ∈ ({x | Feasible e x} : Set (Fin n → ℝ)).extremePoints ℝ := by
  refine ⟨point_feasible e he he2 n bits, ?_⟩
  intro y hy z hz hseg
  obtain ⟨a,b,ha,hb,hab,heq⟩ := hseg
  exact (point_combo e n bits y z a b ha hb hab hy hz heq).1

end TriangularFamily

namespace Hirsch.TriangularCompletion

open Set TriangularFamily

/-- Affine lower/upper boundary lift of the actual triangular system. -/
def lift {n : ℕ} (e : ℝ) (b : Bool) (x : Fin n → ℝ) : Fin (n+1) → ℝ :=
  Fin.cons (branch e b (lead n x)) x

lemma lead_bounds {e : ℝ} {n : ℕ} {x : Fin n → ℝ} (hx : Feasible e x) :
    0 ≤ lead n x ∧ lead n x ≤ 1 := by
  cases n with
  | zero => simp [lead]
  | succ n => exact hx.1 0

lemma lead_mix {n : ℕ} (x y : Fin n → ℝ) (s t : ℝ) :
    lead n (s • x+t • y) = s*lead n x+t*lead n y := by
  cases n <;> simp [lead, Pi.add_apply, Pi.smul_apply, smul_eq_mul]

lemma lift_mix {n : ℕ} (e : ℝ) (b : Bool) (x y : Fin n → ℝ)
    (s t : ℝ) (hst : s+t=1) :
    lift e b (s • x+t • y) = s • lift e b x+t • lift e b y := by
  funext i
  refine Fin.cases ?_ (fun j => rfl) i
  change branch e b (lead n (s • x+t • y)) =
    s*branch e b (lead n x)+t*branch e b (lead n y)
  rw [lead_mix]
  cases b with
  | false => change e*(s*lead n x+t*lead n y)=s*(e*lead n x)+t*(e*lead n y); ring
  | true =>
    change 1-e*(s*lead n x+t*lead n y)=s*(1-e*lead n x)+t*(1-e*lead n y)
    calc
      1-e*(s*lead n x+t*lead n y) = (s+t)-e*(s*lead n x+t*lead n y) := by rw [hst]
      _ = s*(1-e*lead n x)+t*(1-e*lead n y) := by ring

lemma cons_feasible {n : ℕ} (e h : ℝ) (he : 0 < e) (x : Fin n → ℝ)
    (hx : Feasible e x) (hh : e*lead n x ≤ h ∧ h ≤ 1-e*lead n x) :
    Feasible e (Fin.cons h x) := by
  have hz : 0 ≤ e*lead n x := mul_nonneg he.le (lead_bounds hx).1
  constructor
  · intro i
    refine Fin.cases ?_ (fun j => hx.1 j) i
    change 0 ≤ h ∧ h ≤ 1
    constructor <;> linarith
  · intro i j hij
    cases i using Fin.cases with
    | zero =>
      cases n with
      | zero => have hj := j.isLt; simp only [Fin.val_zero] at hij; omega
      | succ n =>
        have hj : j = (0 : Fin (n+1)).succ := by
          apply Fin.ext
          simpa only [Fin.val_zero, Fin.val_succ, zero_add] using hij.symm
        subst j
        exact hh
    | succ i =>
      cases j using Fin.cases with
      | zero => simp only [Fin.val_zero, Fin.val_succ] at hij; omega
      | succ j => exact hx.2 i j (by simp only [Fin.val_succ] at hij; omega)

lemma lift_feasible {n : ℕ} (e : ℝ) (he : 0 < e) (he2 : e < 1/2)
    (b : Bool) (x : Fin n → ℝ) (hx : Feasible e x) : Feasible e (lift e b x) := by
  exact cons_feasible e _ he x hx
    (TriangularFamily.branch_interval e (lead n x) b he he2 (lead_bounds hx))

lemma point_lift (e : ℝ) (n : ℕ) (b : Bool) (bits : Fin n → Bool) :
    lift e b (TriangularFamily.point e n bits) =
      TriangularFamily.point e (n+1) (Fin.cons b bits) := by
  funext i
  refine Fin.cases ?_ (fun j => rfl) i
  change branch e b (lead n (TriangularFamily.point e n bits)) =
    branch e b (level e n bits)
  rw [TriangularFamily.lead_point]

lemma feasible_convex (e : ℝ) (n : ℕ) :
    Convex ℝ {x : Fin n → ℝ | Feasible e x} := by
  intro x hx y hy s t hs ht hst
  constructor
  · intro i
    change 0 ≤ s*x i+t*y i ∧ s*x i+t*y i ≤ 1
    refine ⟨add_nonneg (mul_nonneg hs (hx.1 i).1) (mul_nonneg ht (hy.1 i).1),?_⟩
    calc
      s*x i+t*y i ≤ s*1+t*1 := add_le_add
        (mul_le_mul_of_nonneg_left (hx.1 i).2 hs)
        (mul_le_mul_of_nonneg_left (hy.1 i).2 ht)
      _ = 1 := by simpa only [mul_one] using hst
  · intro i j hij
    have hxi := hx.2 i j hij
    have hyi := hy.2 i j hij
    change e*(s*x j+t*y j) ≤ s*x i+t*y i ∧
      s*x i+t*y i ≤ 1-e*(s*x j+t*y j)
    constructor
    · calc
        e*(s*x j+t*y j) = s*(e*x j)+t*(e*y j) := by ring
        _ ≤ s*x i+t*y i := add_le_add
          (mul_le_mul_of_nonneg_left hxi.1 hs) (mul_le_mul_of_nonneg_left hyi.1 ht)
    · calc
        s*x i+t*y i ≤ s*(1-e*x j)+t*(1-e*y j) := add_le_add
          (mul_le_mul_of_nonneg_left hxi.2 hs) (mul_le_mul_of_nonneg_left hyi.2 ht)
        _ = (s+t)-e*(s*x j+t*y j) := by ring
        _ = 1-e*(s*x j+t*y j) := by rw [hst]

noncomputable def corners (e : ℝ) (n : ℕ) : Finset (Fin n → ℝ) := by
  classical
  exact Finset.univ.image (TriangularFamily.point e n)

lemma lift_mem_hull {n : ℕ} (e : ℝ) (b : Bool) (y : Fin n → ℝ)
    (hy : y ∈ convexHull ℝ (corners e n : Set (Fin n → ℝ))) :
    lift e b y ∈ convexHull ℝ (corners e (n+1) : Set (Fin (n+1) → ℝ)) := by
  classical
  let H := convexHull ℝ (corners e (n+1) : Set (Fin (n+1) → ℝ))
  have hsub : (corners e n : Set (Fin n → ℝ)) ⊆ {x | lift e b x ∈ H} := by
    intro x hx
    obtain ⟨bits,_,rfl⟩ := Finset.mem_image.mp hx
    apply subset_convexHull ℝ _
    exact Finset.mem_image.mpr ⟨Fin.cons b bits,Finset.mem_univ _,(point_lift e n b bits).symm⟩
  have hcv : Convex ℝ {x : Fin n → ℝ | lift e b x ∈ H} := by
    intro x hx z hz s t hs ht hst
    change lift e b (s • x+t • z) ∈ H
    rw [lift_mix e b x z s t hst]
    exact (convex_convexHull ℝ _) hx hz hs ht hst
  exact (convexHull_min hsub hcv) hy

/-- The entire original H body, not just a selected vertex family, is a finite hull. -/
theorem hull_eq_body (e : ℝ) (he : 0 < e) (he2 : e < 1/2) :
    ∀ n, convexHull ℝ (corners e n : Set (Fin n → ℝ)) = {x | Feasible e x} := by
  classical
  have hforward : ∀ n, convexHull ℝ (corners e n : Set (Fin n → ℝ)) ⊆
      {x | Feasible e x} := by
    intro n
    apply convexHull_min _ (feasible_convex e n)
    intro x hx
    obtain ⟨bits,_,rfl⟩ := Finset.mem_image.mp hx
    exact TriangularFamily.point_feasible e he he2 n bits
  intro n
  induction n with
  | zero =>
    apply Set.Subset.antisymm (hforward 0)
    intro x _
    apply subset_convexHull ℝ _
    refine Finset.mem_image.mpr ⟨(fun i : Fin 0 => Fin.elim0 i),Finset.mem_univ _,?_⟩
    funext i
    exact Fin.elim0 i
  | succ n ih =>
    apply Set.Subset.antisymm (hforward (n+1))
    intro x hx
    have htail : tail x ∈ convexHull ℝ (corners e n : Set (Fin n → ℝ)) := by
      rw [ih]
      exact TriangularFamily.tail_feasible hx
    have hl := lift_mem_hull e false (tail x) htail
    have hu := lift_mem_hull e true (tail x) htail
    have hhead := TriangularFamily.head_interval hx
    have hb := lead_bounds (TriangularFamily.tail_feasible hx)
    have hel : e*lead n (tail x) ≤ e :=
      (mul_le_mul_of_nonneg_left hb.2 he.le).trans_eq (mul_one e)
    have hden : 0 < 1-2*e*lead n (tail x) := by nlinarith
    let t : ℝ := (x 0-e*lead n (tail x))/(1-2*e*lead n (tail x))
    have ht0 : 0 ≤ t := div_nonneg (sub_nonneg.mpr hhead.1) hden.le
    have ht1 : t ≤ 1 := (div_le_one hden).mpr (by linarith [hhead.2])
    have hmul : t*(1-2*e*lead n (tail x)) = x 0-e*lead n (tail x) :=
      div_mul_cancel₀ _ (ne_of_gt hden)
    have hcombo : (1-t) • lift e false (tail x)+t • lift e true (tail x) = x := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · change (1-t)*(e*lead n (tail x))+t*(1-e*lead n (tail x))=x 0
        calc
          (1-t)*(e*lead n (tail x))+t*(1-e*lead n (tail x)) =
            e*lead n (tail x)+t*(1-2*e*lead n (tail x)) := by ring
          _ = x 0 := by rw [hmul]; ring
      · change (1-t)*x j.succ+t*x j.succ=x j.succ
        ring
    exact hcombo ▸ (convex_convexHull ℝ _) hl hu (sub_nonneg.mpr ht1) ht0 (by ring)

/-- A line obtained by fixing every earlier boundary choice and freeing the last coordinate. -/
def line (e : ℝ) : (n : ℕ) → (Fin n → Bool) → ℝ → (Fin (n+1) → ℝ)
  | 0, _, t => fun _ => t
  | n+1, bits, t => lift e (bits 0) (line e n (tail bits) t)

lemma line_feasible (e : ℝ) (he : 0 < e) (he2 : e < 1/2) :
    ∀ n (bits : Fin n → Bool) t, 0 ≤ t → t ≤ 1 → Feasible e (line e n bits t) := by
  intro n
  induction n with
  | zero =>
    intro bits t ht0 ht1
    refine ⟨fun _ => ⟨ht0,ht1⟩,?_⟩
    intro i j hij
    have hi := i.isLt
    have hj := j.isLt
    omega
  | succ n ih =>
    intro bits t ht0 ht1
    exact lift_feasible e he he2 (bits 0) _ (ih (tail bits) t ht0 ht1)

lemma line_mix (e : ℝ) : ∀ n (bits : Fin n → Bool) a b s t, s+t=1 →
    line e n bits (s*a+t*b) = s • line e n bits a+t • line e n bits b := by
  intro n
  induction n with
  | zero =>
    intro bits a b s t hst
    funext i
    rfl
  | succ n ih =>
    intro bits a b s t hst
    change lift e (bits 0) (line e n (tail bits) (s*a+t*b)) =
      s • lift e (bits 0) (line e n (tail bits) a)+t • lift e (bits 0) (line e n (tail bits) b)
    rw [ih (tail bits) a b s t hst, lift_mix e (bits 0) _ _ s t hst]

lemma line_last (e : ℝ) : ∀ n (bits : Fin n → Bool) t,
    line e n bits t (Fin.last n) = t := by
  intro n
  induction n with
  | zero => intros; rfl
  | succ n ih =>
    intro bits t
    change line e n (tail bits) t (Fin.last n) = t
    exact ih (tail bits) t

lemma line_mem_segment (e : ℝ) (n : ℕ) (bits : Fin n → Bool)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    line e n bits t ∈ segment ℝ (line e n bits 0) (line e n bits 1) := by
  refine ⟨1-t,t,sub_nonneg.mpr ht1,ht0,by ring,?_⟩
  simpa only [mul_zero, mul_one, zero_add] using
    (line_mix e n bits 0 1 (1-t) t (by ring)).symm

lemma line_ne (e : ℝ) (n : ℕ) (bits : Fin n → Bool) :
    line e n bits 0 ≠ line e n bits 1 := by
  intro h
  have hh := congrFun h (Fin.last n)
  rw [line_last,line_last] at hh
  norm_num at hh

 def tailLinear (n : ℕ) : (Fin (n+1) → ℝ) →ₗ[ℝ] (Fin n → ℝ) where
  toFun := tail
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def chosenRow (e : ℝ) (n : ℕ) (b : Bool) : (Fin (n+2) → ℝ) →ₗ[ℝ] ℝ where
  toFun x := if b then x 0+e*x (0 : Fin (n+1)).succ else -x 0+e*x (0 : Fin (n+1)).succ
  map_add' x y := by cases b <;> simp <;> ring
  map_smul' s x := by cases b <;> simp [smul_eq_mul] <;> ring

lemma row_lift (e : ℝ) (n : ℕ) (b : Bool) (y : Fin (n+1) → ℝ) :
    chosenRow e n b (lift e b y) = (if b then 1 else 0 : ℝ) := by
  cases b with
  | false => change -(e*y 0)+e*y 0=0; ring
  | true => change (1-e*y 0)+e*y 0=1; ring

lemma row_bound (e : ℝ) (n : ℕ) (b : Bool) (x : Fin (n+2) → ℝ)
    (hx : Feasible e x) : chosenRow e n b x ≤ (if b then 1 else 0 : ℝ) := by
  have h := TriangularFamily.head_interval hx
  change e*x (0 : Fin (n+1)).succ ≤ x 0 ∧ x 0 ≤ 1-e*x (0 : Fin (n+1)).succ at h
  cases b with
  | false => change -x 0+e*x (0 : Fin (n+1)).succ ≤ 0; linarith
  | true => change x 0+e*x (0 : Fin (n+1)).succ ≤ 1; linarith

lemma row_eq_lift (e : ℝ) (n : ℕ) (b : Bool) (x : Fin (n+2) → ℝ)
    (h : chosenRow e n b x = (if b then 1 else 0 : ℝ)) : x = lift e b (tail x) := by
  funext i
  refine Fin.cases ?_ (fun j => rfl) i
  cases b with
  | false =>
    change -x 0+e*x (0 : Fin (n+1)).succ=0 at h
    change x 0=e*x (0 : Fin (n+1)).succ
    linarith
  | true =>
    change x 0+e*x (0 : Fin (n+1)).succ=1 at h
    change x 0=1-e*x (0 : Fin (n+1)).succ
    linarith

/-- The sum of chosen original rows exposes exactly the selected one-dimensional slice. -/
theorem supporting_line (e : ℝ) : ∀ n (bits : Fin n → Bool),
    ∃ f : (Fin (n+1) → ℝ) →ₗ[ℝ] ℝ, ∃ M : ℝ,
      (∀ t, f (line e n bits t)=M) ∧
      ∀ x, Feasible e x → f x ≤ M ∧
        (f x=M → ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ line e n bits t=x) := by
  intro n
  induction n with
  | zero =>
    intro bits
    refine ⟨0,0,fun _ => rfl,?_⟩
    intro x hx
    refine ⟨le_rfl,fun _ => ⟨x 0,(hx.1 0).1,(hx.1 0).2,?_⟩⟩
    funext i
    have hi : i = (0 : Fin 1) := by
      apply Fin.ext
      change i.val = 0
      have hiBound := i.isLt
      omega
    subst i
    rfl
  | succ n ih =>
    intro bits
    obtain ⟨f,M,hline,hbound⟩ := ih (tail bits)
    let R := chosenRow e n (bits 0)
    let B : ℝ := if bits 0 then 1 else 0
    let g : (Fin (n+2) → ℝ) →ₗ[ℝ] ℝ := R+f.comp (tailLinear (n+1))
    refine ⟨g,B+M,?_,?_⟩
    · intro t
      change chosenRow e n (bits 0) (lift e (bits 0) (line e n (tail bits) t))+
        f (line e n (tail bits) t)=B+M
      rw [row_lift,hline]
    · intro x hx
      have hr := row_bound e n (bits 0) x hx
      have ht := hbound (tail x) (TriangularFamily.tail_feasible hx)
      change R x ≤ B at hr
      change R x+f (tail x) ≤ B+M ∧ (R x+f (tail x)=B+M → _)
      refine ⟨add_le_add hr ht.1,?_⟩
      intro heq
      have heR : R x=B := by linarith
      have heT : f (tail x)=M := by linarith
      obtain ⟨t,ht0,ht1,heTail⟩ := ht.2 heT
      refine ⟨t,ht0,ht1,?_⟩
      change lift e (bits 0) (line e n (tail bits) t)=x
      rw [heTail]
      exact (row_eq_lift e n (bits 0) x heR).symm

/-- Each selected slice is a genuine nondegenerate exposed edge of the original H body. -/
theorem exposed_line (e : ℝ) (he : 0 < e) (he2 : e < 1/2)
    (n : ℕ) (bits : Fin n → Bool) :
    IsExposed ℝ {x : Fin (n+1) → ℝ | Feasible e x}
      (segment ℝ (line e n bits 0) (line e n bits 1)) := by
  obtain ⟨f,M,hline,hbound⟩ := supporting_line e n bits
  have h0 := line_feasible e he he2 n bits 0 le_rfl (by norm_num)
  have h1 := line_feasible e he he2 n bits 1 (by norm_num) le_rfl
  intro _
  refine ⟨f.toContinuousLinearMap,?_⟩
  ext x
  constructor
  · intro hx
    obtain ⟨s,t,hs,ht,hst,heq⟩ := hx
    have hxP : Feasible e x := heq ▸ (feasible_convex e (n+1)) h0 h1 hs ht hst
    have hfx : f x=M := by
      rw [← heq,map_add,map_smul,map_smul,hline,hline]
      change s*M+t*M=M
      rw [← add_mul,hst,one_mul]
    refine ⟨hxP,?_⟩
    intro y hy
    change f y ≤ f x
    rw [hfx]
    exact (hbound y hy).1
  · rintro ⟨hx,hmax⟩
    have hlow := hmax (line e n bits 0) h0
    change f (line e n bits 0) ≤ f x at hlow
    rw [hline] at hlow
    have heq : f x=M := le_antisymm (hbound x hx).1 hlow
    obtain ⟨t,ht0,ht1,htx⟩ := (hbound x hx).2 heq
    exact htx ▸ line_mem_segment e n bits t ht0 ht1

def delta (e : ℝ) (n : ℕ) (bits : Fin n → Bool) : Fin (n+1) → ℝ :=
  line e n bits 1-line e n bits 0

lemma delta_last (e : ℝ) (n : ℕ) (bits : Fin n → Bool) : delta e n bits (Fin.last n)=1 := by
  change line e n bits 1 (Fin.last n)-line e n bits 0 (Fin.last n)=1
  rw [line_last,line_last]
  norm_num

lemma delta_head (e : ℝ) (n : ℕ) (bits : Fin (n+1) → Bool) :
    delta e (n+1) bits 0 = (if bits 0 then -e else e)*delta e n (tail bits) 0 := by
  change branch e (bits 0) (line e n (tail bits) 1 0)-
    branch e (bits 0) (line e n (tail bits) 0 0) =
    (if bits 0 then -e else e)*(line e n (tail bits) 1 0-line e n (tail bits) 0 0)
  cases hb : bits 0 with
  | false =>
    change e*line e n (tail bits) 1 0-e*line e n (tail bits) 0 0 =
      e*(line e n (tail bits) 1 0-line e n (tail bits) 0 0)
    ring
  | true =>
    change (1-e*line e n (tail bits) 1 0)-(1-e*line e n (tail bits) 0 0) =
      (-e)*(line e n (tail bits) 1 0-line e n (tail bits) 0 0)
    ring

lemma delta_head_ne (e : ℝ) (he : e ≠ 0) : ∀ n (bits : Fin n → Bool), delta e n bits 0 ≠ 0 := by
  intro n
  induction n with
  | zero => intro bits; change (1 : ℝ)-0 ≠ 0; norm_num
  | succ n ih =>
    intro bits
    rw [delta_head]
    apply mul_ne_zero _ (ih (tail bits))
    cases hb : bits 0
    · exact he
    · exact neg_ne_zero.mpr he

lemma delta_injective (e : ℝ) (he : 0 < e) : ∀ n, Function.Injective (delta e n) := by
  intro n
  induction n with
  | zero => intro a b _; funext i; exact Fin.elim0 i
  | succ n ih =>
    intro a b hab
    have htail : delta e n (tail a)=delta e n (tail b) := by
      funext i
      exact congrFun hab i.succ
    have hbits : tail a=tail b := ih htail
    have hh := congrFun hab 0
    rw [delta_head,delta_head,hbits] at hh
    have hc := mul_right_cancel₀ (delta_head_ne e (ne_of_gt he) n (tail b)) hh
    have hhead : a 0=b 0 := by
      cases ha : a 0 <;> cases hb : b 0
      · rfl
      · have h : e = -e := by simpa [ha,hb] using hc
        exact False.elim ((ne_of_gt he) (by linarith))
      · have h : -e = e := by simpa [ha,hb] using hc
        exact False.elim ((ne_of_gt he) (by linarith))
      · rfl
    funext i
    exact Fin.cases hhead (fun j => congrFun hbits j) i

/-- Last-coordinate normalization turns direction parallelism into equality of all bits. -/
theorem directions_separate (e : ℝ) (he : 0 < e) (n : ℕ)
    (a b : Fin n → Bool) (c : ℝ) (hab : delta e n a=c • delta e n b) : a=b := by
  have hh := congrFun hab (Fin.last n)
  change delta e n a (Fin.last n)=c*delta e n b (Fin.last n) at hh
  rw [delta_last,delta_last,mul_one] at hh
  have hc : c=1 := hh.symm
  rw [hc,one_smul] at hab
  exact delta_injective e he n hab

/-- Only the last coordinate's box bounds are needed: this is exactly 2(n+1) inequalities. -/
def minimalBody (e : ℝ) (n : ℕ) : Set (Fin (n+1) → ℝ) :=
  {x | (0 ≤ x (Fin.last n) ∧ x (Fin.last n) ≤ 1) ∧
    ∀ i : Fin n, e*x i.succ ≤ x i.castSucc ∧ x i.castSucc ≤ 1-e*x i.succ}

theorem minimal_eq_body (e : ℝ) (he : 0 < e) (n : ℕ) :
    minimalBody e n = {x : Fin (n+1) → ℝ | Feasible e x} := by
  ext x
  constructor
  · intro hx
    have hbounds : ∀ k : ℕ, ∀ i : Fin (n+1), i.val+k=n → 0 ≤ x i ∧ x i ≤ 1 := by
      intro k
      induction k with
      | zero =>
        intro i hi
        have hi' : i=Fin.last n := by
          apply Fin.ext
          change i.val = n
          omega
        rw [hi']
        exact hx.1
      | succ k ih =>
        intro i hi
        have hin : i.val<n := by omega
        let j : Fin n := ⟨i.val,hin⟩
        have hb := ih j.succ (by change i.val+1+k=n; omega)
        have hrow := hx.2 j
        have heq : j.castSucc=i := Fin.ext rfl
        rw [heq] at hrow
        have hz := mul_nonneg he.le hb.1
        constructor <;> linarith
    refine ⟨fun i => hbounds (n-i.val) i (by have hi := i.isLt; omega),?_⟩
    intro i j hij
    have hin : i.val<n := by have hj := j.isLt; omega
    let k : Fin n := ⟨i.val,hin⟩
    have hik : k.castSucc=i := Fin.ext rfl
    have hjk : k.succ=j := Fin.ext hij
    have h := hx.2 k
    rw [hik,hjk] at h
    exact h
  · intro hx
    exact ⟨hx.1 (Fin.last n),fun i => hx.2 i.castSucc i.succ rfl⟩

/-- Instantiate direction inheritance on a constructed exponential original-edge family. -/
theorem exponential_completion (e : ℝ) (he : 0 < e) (he2 : e < 1/2) (n m : ℕ)
    (Q : Set (Fin (n+1) → ℝ)) (hQc : IsCompact Q) (hQne : Q.Nonempty)
    (w : Fin m → (Fin (n+1) → ℝ))
    (hZ : {z | ∃ x ∈ minimalBody e n, ∃ y ∈ Q, x+y=z}=ZonotopeWall.body w) :
    2^n ≤ m ∧ ∃ u v : Fin (n+1) → ℝ,
      u ∈ (ZonotopeWall.body w).extremePoints ℝ ∧
      v ∈ (ZonotopeWall.body w).extremePoints ℝ ∧ u+v=∑ i : Fin m, w i ∧
      ∀ L : ℕ, ∀ p : Fin (L+1) → (Fin (n+1) → ℝ),
        p 0=u → p (Fin.last L)=v → (∀ i, p i ∈ ZonotopeWall.body w) →
        (∀ i : Fin L, p i.castSucc ≠ p i.succ ∧
          IsExposed ℝ (ZonotopeWall.body w) (segment ℝ (p i.castSucc) (p i.succ))) → 2^n ≤ L := by
  classical
  let I := Fin n → Bool
  let E := Fintype.equivFin I
  let a : Fin (Fintype.card I) → (Fin (n+1) → ℝ) := fun i => line e n (E.symm i) 0
  let b : Fin (Fintype.card I) → (Fin (n+1) → ℝ) := fun i => line e n (E.symm i) 1
  have hC : convexHull ℝ (corners e (n+1) : Set (Fin (n+1) → ℝ))=minimalBody e n := by
    rw [hull_eq_body e he he2, minimal_eq_body e he]
  have hz : {z | ∃ x ∈ convexHull ℝ (corners e (n+1) : Set (Fin (n+1) → ℝ)),
      ∃ y ∈ Q, x+y=z}=ZonotopeWall.body w := by rw [hC]; exact hZ
  have hedge : ∀ i, a i ∈ convexHull ℝ (corners e (n+1) : Set (Fin (n+1) → ℝ)) ∧
      b i ∈ convexHull ℝ (corners e (n+1) : Set (Fin (n+1) → ℝ)) ∧ a i ≠ b i ∧
      IsExposed ℝ (convexHull ℝ (corners e (n+1) : Set (Fin (n+1) → ℝ)))
        (segment ℝ (a i) (b i)) := by
    intro i
    rw [hull_eq_body e he he2]
    exact ⟨line_feasible e he he2 n _ 0 le_rfl (by norm_num),
      line_feasible e he he2 n _ 1 (by norm_num) le_rfl,
      line_ne e n _, exposed_line e he he2 n _⟩
  have hdirs : ∀ i j : Fin (Fintype.card I), ∀ c : ℝ, b i-a i=c • (b j-a j) → i=j := by
    intro i j c hc
    apply E.symm.injective
    exact directions_separate e he n (E.symm i) (E.symm j) c hc
  obtain ⟨_,hcount,u,v,hu,hv,huv,hwalk⟩ := CompletionDirections.completion_lower_bound
    (corners e (n+1)) Q hQc hQne w hz a b hedge hdirs
  have hcard : Fintype.card I=2^n := by simp [I]
  refine ⟨by simpa only [hcard] using hcount,u,v,hu,hv,huv,?_⟩
  intro L p hp0 hpL hmem heds
  simpa only [hcard] using hwalk L p hp0 hpL hmem heds

end Hirsch.TriangularCompletion

/-- A linearly presented original triangular H family forces exponentially
many directions and intrinsic steps in every compact-summand zonotope completion. -/
theorem solution (e : ℝ) (he : 0 < e) (he2 : e < 1/2) (n m : ℕ)
    (Q : Set (Fin (n+1) → ℝ)) (hQc : IsCompact Q) (hQne : Q.Nonempty)
    (w : Fin m → (Fin (n+1) → ℝ)) :
    let P : Set (Fin (n+1) → ℝ) := {x |
      (0 ≤ x (Fin.last n) ∧ x (Fin.last n) ≤ 1) ∧
      ∀ i : Fin n, e*x i.succ ≤ x i.castSucc ∧ x i.castSucc ≤ 1-e*x i.succ}
    let Z : Set (Fin (n+1) → ℝ) := {x | ∃ s : Fin m → ℝ,
      (∀ i, 0 ≤ s i ∧ s i ≤ 1) ∧ (∑ i : Fin m, s i • w i)=x}
    {z | ∃ x ∈ P, ∃ y ∈ Q, x+y=z}=Z →
    2^n ≤ m ∧ ∃ u v : Fin (n+1) → ℝ,
      u ∈ Z.extremePoints ℝ ∧ v ∈ Z.extremePoints ℝ ∧ u+v=∑ i : Fin m, w i ∧
      ∀ L : ℕ, ∀ p : Fin (L+1) → (Fin (n+1) → ℝ),
        p 0=u → p (Fin.last L)=v → (∀ i, p i ∈ Z) →
        (∀ i : Fin L, p i.castSucc ≠ p i.succ ∧
          IsExposed ℝ Z (segment ℝ (p i.castSucc) (p i.succ))) → 2^n ≤ L := by
  dsimp only
  intro hZ
  exact Hirsch.TriangularCompletion.exponential_completion e he he2 n m Q hQc hQne w hZ

#print axioms Hirsch.TriangularCompletion.hull_eq_body
#print axioms Hirsch.TriangularCompletion.exposed_line
#print axioms Hirsch.TriangularCompletion.directions_separate
#print axioms Hirsch.TriangularCompletion.minimal_eq_body
#print axioms Hirsch.TriangularCompletion.exponential_completion
#print axioms solution
