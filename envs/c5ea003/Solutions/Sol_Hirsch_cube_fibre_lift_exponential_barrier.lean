-- Prove2me | solution 1 for Hirsch.cube_fibre_lift_exponential_barrier
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-20T13:22:23.939857+00:00
-- url     : https://prove2.me/submissions/4581df96-9ce6-4bdd-bb5e-5e974589db39

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

end Hirsch.ZonotopeDirections

namespace Hirsch.CubeLiftBarrier

open Set ZonotopeWall ZonotopeDirections

lemma update_point {d m : ℕ} (w : Fin m → (Fin d → ℝ))
    (s : Fin m → ℝ) (i : Fin m) (c : ℝ) :
    point w (Function.update s i c) = point w s + (c-s i) • w i := by
  classical
  have hd : point w (Function.update s i c)-point w s = (c-s i) • w i := by
    unfold point
    rw [← Finset.sum_sub_distrib, Finset.sum_eq_single i]
    · simp only [Function.update_self]
      module
    · intro j _ hji
      simp only [Function.update_of_ne hji, sub_self]
    · intro hn
      exact False.elim (hn (Finset.mem_univ i))
  rw [← hd]
  abel

lemma update_bounds {m : ℕ} (s : Fin m → ℝ)
    (hs : ∀ j, 0 ≤ s j ∧ s j ≤ 1) (i : Fin m) (c : ℝ) (hc : 0 ≤ c ∧ c ≤ 1) :
    ∀ j, 0 ≤ Function.update s i c j ∧ Function.update s i c j ≤ 1 := by
  intro j
  by_cases hji : j=i
  · subst j
    simpa only [Function.update_self] using hc
  · simpa only [Function.update_of_ne hji] using hs j

/-- A feasible forward generator segment at an extreme point forces the
corresponding coefficient to vanish in EVERY feasible representation. -/
theorem lower_saturation {d m : ℕ} (w : Fin m → (Fin d → ℝ))
    (s : Fin m → ℝ) (hs : ∀ i, 0 ≤ s i ∧ s i ≤ 1)
    (hu : point w s ∈ (body w).extremePoints ℝ)
    (i : Fin m) (hwi : w i ≠ 0)
    (hforward : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → point w s + t • w i ∈ body w) : s i=0 := by
  by_cases hsi : s i=0
  · exact hsi
  have hpos : 0 < s i := lt_of_le_of_ne (hs i).1 (Ne.symm hsi)
  have hminus : point w s - s i • w i ∈ body w := by
    have hm : point w (Function.update s i 0) ∈ body w :=
      ⟨_,update_bounds s hs i 0 ⟨le_rfl,by norm_num⟩,rfl⟩
    rw [update_point] at hm
    simpa only [zero_sub,neg_smul,← sub_eq_add_neg] using hm
  have hplus := hforward (s i) (hs i).1 (hs i).2
  have hmid : point w s ∈ openSegment ℝ
      (point w s + s i • w i) (point w s - s i • w i) := by
    refine ⟨(1/2 : ℝ),(1/2 : ℝ),by norm_num,by norm_num,by norm_num,?_⟩
    module
  have he := hu.2 hplus hminus hmid
  have hz : s i • w i = 0 := add_left_cancel (he.trans (add_zero _).symm)
  exact (smul_eq_zero.mp hz).resolve_right hwi

/-- The reverse feasible segment similarly forces coefficient one. -/
theorem upper_saturation {d m : ℕ} (w : Fin m → (Fin d → ℝ))
    (s : Fin m → ℝ) (hs : ∀ i, 0 ≤ s i ∧ s i ≤ 1)
    (hu : point w s ∈ (body w).extremePoints ℝ)
    (i : Fin m) (hwi : w i ≠ 0)
    (hback : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → point w s - t • w i ∈ body w) : s i=1 := by
  by_cases hsi : s i=1
  · exact hsi
  have he0 : 0 ≤ 1-s i := sub_nonneg.mpr (hs i).2
  have he1 : 1-s i ≤ 1 := by linarith [(hs i).1]
  have hplus : point w s + (1-s i) • w i ∈ body w := by
    have hm : point w (Function.update s i 1) ∈ body w :=
      ⟨_,update_bounds s hs i 1 ⟨by norm_num,le_rfl⟩,rfl⟩
    simpa only [update_point] using hm
  have hminus := hback (1-s i) he0 he1
  have hmid : point w s ∈ openSegment ℝ
      (point w s + (1-s i) • w i) (point w s - (1-s i) • w i) := by
    refine ⟨(1/2 : ℝ),(1/2 : ℝ),by norm_num,by norm_num,by norm_num,?_⟩
    module
  have he := hu.2 hplus hminus hmid
  have hz : (1-s i) • w i = 0 := add_left_cancel (he.trans (add_zero _).symm)
  have hscalar := (smul_eq_zero.mp hz).resolve_right hwi
  linarith

noncomputable def binary {d : ℕ} (S : Finset (Fin d)) : Fin d → ℝ :=
  fun j => if j ∈ S then 1 else 0

lemma binary_ne_zero {d : ℕ} (S : Finset (Fin d)) (hS : S.Nonempty) : binary S ≠ 0 := by
  classical
  obtain ⟨j,hj⟩ := hS
  intro hz
  have he := congrFun hz j
  have hbad : (1 : ℝ)=0 := by simpa only [binary,if_pos hj,Pi.zero_apply] using he
  norm_num at hbad

/-- Nonempty zero-one vectors determine distinct unoriented directions. -/
theorem binary_parallel {d : ℕ} (S T : Finset (Fin d)) (hS : S.Nonempty)
    (c : ℝ) (he : binary S = c • binary T) : S=T := by
  classical
  obtain ⟨j,hj⟩ := hS
  have hc : c=1 := by
    have h := congrFun he j
    change (if j ∈ S then (1 : ℝ) else 0) = c*(if j ∈ T then 1 else 0) at h
    rw [if_pos hj] at h
    by_cases hjT : j ∈ T
    · simpa only [if_pos hjT,mul_one] using h.symm
    · simp only [if_neg hjT,mul_zero] at h
      norm_num at h
  rw [hc,one_smul] at he
  ext i
  have h := congrFun he i
  by_cases hiS : i ∈ S <;> by_cases hiT : i ∈ T
  · exact iff_of_true hiS hiT
  · simp only [binary,if_pos hiS,if_neg hiT] at h
    norm_num at h
  · simp only [binary,if_neg hiS,if_pos hiT] at h
    norm_num at h
  · exact iff_of_false hiS hiT

/-- EVERY compatible endpoint lift is separated by exponentially many distinct
positive Boolean generator directions. This is not just a global diameter pair. -/
theorem every_cube_lift_route {d m : ℕ} (w : Fin m → (Fin d → ℝ))
    (label : Finset (Fin d) → Fin m)
    (hlabel : ∀ S, S.Nonempty → w (label S)=binary S)
    (Q : Set (Fin d → ℝ)) (q₀ q₁ : Fin d → ℝ)
    (hq₀ : q₀ ∈ Q) (hq₁ : q₁ ∈ Q)
    (hcontains : ∀ x : Fin d → ℝ, (∀ j, 0 ≤ x j ∧ x j ≤ 1) →
      ∀ q ∈ Q, x+q ∈ body w)
    (hu : q₀ ∈ (body w).extremePoints ℝ)
    (hv : (fun _ : Fin d => (1 : ℝ))+q₁ ∈ (body w).extremePoints ℝ)
    (L : ℕ) (p : Fin (L+1) → (Fin d → ℝ))
    (hp₀ : p 0=q₀) (hp₁ : p (Fin.last L)=(fun _ => (1 : ℝ))+q₁)
    (hmem : ∀ i, p i ∈ body w)
    (hedge : ∀ i : Fin L, p i.castSucc ≠ p i.succ ∧
      IsExposed ℝ (body w) (segment ℝ (p i.castSucc) (p i.succ))) : 2^d ≤ L+1 := by
  classical
  let T : Finset (Finset (Fin d)) := Finset.univ.erase ∅
  have hnonempty : ∀ S : T, S.val.Nonempty := by
    intro S
    exact Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp S.property).1
  have hnonzero : ∀ S : T, w (label S.val) ≠ 0 := by
    intro S
    rw [hlabel S.val (hnonempty S)]
    exact binary_ne_zero S.val (hnonempty S)
  have hcoeff : ∀ i : Fin (L+1), ∃ s : Fin m → ℝ,
      (∀ j, 0 ≤ s j ∧ s j ≤ 1) ∧ point w s=p i := fun i => hmem i
  choose s hs hpoint using hcoeff
  have hfirst : ∀ S : T, s 0 (label S.val)=0 := by
    intro S
    apply lower_saturation w (s 0) (hs 0) (by rw [hpoint,hp₀]; exact hu)
      (label S.val) (hnonzero S)
    intro t ht0 ht1
    rw [hpoint,hp₀,hlabel S.val (hnonempty S),add_comm]
    apply hcontains _ _ q₀ hq₀
    intro j
    change 0 ≤ t*(if j ∈ S.val then (1 : ℝ) else 0) ∧
      t*(if j ∈ S.val then (1 : ℝ) else 0) ≤ 1
    by_cases hj : j ∈ S.val
    · simpa only [if_pos hj,mul_one] using And.intro ht0 ht1
    · simp only [if_neg hj,mul_zero]
      norm_num
  have hlast : ∀ S : T, s (Fin.last L) (label S.val)=1 := by
    intro S
    apply upper_saturation w (s (Fin.last L)) (hs (Fin.last L))
      (by rw [hpoint,hp₁]; exact hv) (label S.val) (hnonzero S)
    intro t ht0 ht1
    rw [hpoint,hp₁,hlabel S.val (hnonempty S)]
    have he : (fun _ : Fin d => (1 : ℝ))+q₁-t • binary S.val =
        ((fun _ : Fin d => (1 : ℝ))-t • binary S.val)+q₁ := by abel
    rw [he]
    apply hcontains _ _ q₁ hq₁
    intro j
    change 0 ≤ 1-t*(if j ∈ S.val then (1 : ℝ) else 0) ∧
      1-t*(if j ∈ S.val then (1 : ℝ) else 0) ≤ 1
    by_cases hj : j ∈ S.val
    · simp only [if_pos hj,mul_one]
      constructor <;> linarith
    · simp only [if_neg hj,mul_zero,sub_zero]
      norm_num
  have hchanges : ∀ S : T, ∃ i : Fin L,
      s i.castSucc (label S.val) ≠ s i.succ (label S.val) := by
    intro S
    apply exists_change L (fun i => s i (label S.val))
    rw [hfirst S,hlast S]
    norm_num
  choose step hstep using hchanges
  have hinj : Function.Injective step := by
    intro S U hSU
    have hb := hstep U
    rw [← hSU] at hb
    have hne : point w (s (step S).castSucc) ≠ point w (s (step S).succ) := by
      rw [hpoint,hpoint]
      exact (hedge (step S)).1
    have hex : IsExposed ℝ (body w)
        (segment ℝ (point w (s (step S).castSucc)) (point w (s (step S).succ))) := by
      rw [hpoint,hpoint]
      exact (hedge (step S)).2
    obtain ⟨c,hc⟩ := changed_indices_parallel w _ _ (hs _) (hs _) hne hex
      (label S.val) (label U.val) (hnonzero U) (hstep S) hb
    rw [hlabel S.val (hnonempty S),hlabel U.val (hnonempty U)] at hc
    apply Subtype.ext
    exact binary_parallel S.val U.val (hnonempty S) c hc
  have hbound : T.card ≤ L := by
    simpa only [Fintype.card_coe,Fintype.card_fin] using Fintype.card_le_of_injective step hinj
  have hcard : T.card+1=2^d := by
    have he := Finset.card_erase_add_one (Finset.mem_univ (∅ : Finset (Fin d)))
    simpa only [T,Finset.card_univ,Fintype.card_finset,Fintype.card_fin] using he
  omega

end Hirsch.CubeLiftBarrier

/-- Choosing better lifts of opposite cube corners cannot remove this
completion's exponential UNWEIGHTED edge cost. -/
theorem solution (d m : ℕ) (w : Fin m → (Fin d → ℝ))
    (label : Finset (Fin d) → Fin m)
    (hlabel : ∀ S : Finset (Fin d), S.Nonempty → ∀ j,
      w (label S) j = if j ∈ S then 1 else 0)
    (Q : Set (Fin d → ℝ)) (q₀ q₁ : Fin d → ℝ) (hq₀ : q₀ ∈ Q) (hq₁ : q₁ ∈ Q) :
    let Z : Set (Fin d → ℝ) := {z | ∃ s : Fin m → ℝ,
      (∀ i, 0 ≤ s i ∧ s i ≤ 1) ∧ (∑ i : Fin m, s i • w i)=z}
    (∀ x : Fin d → ℝ, (∀ j, 0 ≤ x j ∧ x j ≤ 1) → ∀ q ∈ Q, x+q ∈ Z) →
    q₀ ∈ Z.extremePoints ℝ → (fun _ : Fin d => (1 : ℝ))+q₁ ∈ Z.extremePoints ℝ →
    ∀ L : ℕ, ∀ p : Fin (L+1) → (Fin d → ℝ),
      p 0=q₀ → p (Fin.last L)=(fun _ => (1 : ℝ))+q₁ → (∀ i, p i ∈ Z) →
      (∀ i : Fin L, p i.castSucc ≠ p i.succ ∧
        IsExposed ℝ Z (segment ℝ (p i.castSucc) (p i.succ))) → 2^d ≤ L+1 := by
  dsimp only
  intro hcontains hu hv L p hp₀ hp₁ hmem hedge
  apply Hirsch.CubeLiftBarrier.every_cube_lift_route w label _ Q q₀ q₁ hq₀ hq₁
    hcontains hu hv L p hp₀ hp₁ hmem hedge
  intro S hS
  funext j
  exact hlabel S hS j

#print axioms Hirsch.CubeLiftBarrier.lower_saturation
#print axioms Hirsch.CubeLiftBarrier.upper_saturation
#print axioms Hirsch.CubeLiftBarrier.binary_parallel
#print axioms Hirsch.CubeLiftBarrier.every_cube_lift_route
#print axioms solution
