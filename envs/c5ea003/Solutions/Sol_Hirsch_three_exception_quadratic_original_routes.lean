-- Prove2me | solution 1 for Hirsch.three_exception_quadratic_original_routes
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-22T02:39:18.485074+00:00
-- url     : https://prove2.me/submissions/1dfac8b5-2a3d-42d5-9a66-f4380f08393d

import Mathlib

open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

namespace Hirsch.CoordinateRoute

variable {V : Type*} [DecidableEq V]

/-- A finite walk whose entire visited sequence lies in the specified set. -/
structure Route (R : V → V → Prop) (S : Finset V) (u v : V) where
  length : ℕ
  point : ℕ → V
  first : point 0 = u
  last : point length = v
  mem : ∀ i, i ≤ length → point i ∈ S
  step : ∀ i, i < length → R (point i) (point (i+1))

namespace Route

variable {R : V → V → Prop} {S T : Finset V} {u v w : V}

def nil (hu : u ∈ S) : Route R S u u where
  length := 0
  point := fun _ => u
  first := rfl
  last := rfl
  mem := fun _ _ => hu
  step := by intro i hi; omega

def prepend (hu : u ∈ S) (h : R u v) (p : Route R S v w) : Route R S u w where
  length := p.length+1
  point := fun i => if i = 0 then u else p.point (i-1)
  first := by simp
  last := by simpa using p.last
  mem := by
    intro i hi
    by_cases hz : i = 0
    · simpa [hz] using hu
    · simpa [hz] using p.mem (i-1) (by omega)
  step := by
    intro i hi
    cases i with
    | zero => simpa [p.first] using h
    | succ i => simpa using p.step i (by omega)

def mono (p : Route R S u v) (hST : S ⊆ T) : Route R T u v where
  length := p.length
  point := p.point
  first := p.first
  last := p.last
  mem := fun i hi => hST (p.mem i hi)
  step := p.step

def reverse (p : Route R S u v) (hsym : ∀ a b, R a b → R b a) : Route R S v u where
  length := p.length
  point := fun i => p.point (p.length-i)
  first := by simpa using p.last
  last := by simpa using p.first
  mem := fun i _ => p.mem (p.length-i) (Nat.sub_le _ _)
  step := by
    intro i hi
    have h := hsym _ _ (p.step (p.length-(i+1)) (by omega))
    have he : p.length-(i+1)+1 = p.length-i := by omega
    simpa only [he] using h

def append (p : Route R S u v) (q : Route R S v w) : Route R S u w where
  length := p.length+q.length
  point := fun i => if i ≤ p.length then p.point i else q.point (i-p.length)
  first := by simpa using p.first
  last := by
    by_cases hz : q.length = 0
    · have hvw : v = w := q.first.symm.trans (by simpa [hz] using q.last)
      simpa [hz] using p.last.trans hvw
    · have hn : ¬ p.length+q.length ≤ p.length := by omega
      simpa [hn] using q.last
  mem := by
    intro i hi
    by_cases h : i ≤ p.length
    · simpa only [if_pos h] using p.mem i h
    · simpa only [if_neg h] using q.mem (i-p.length) (by omega)
  step := by
    intro i hi
    by_cases h : i < p.length
    · have h0 : i ≤ p.length := by omega
      have h1 : i+1 ≤ p.length := by omega
      simpa only [if_pos h0, if_pos h1] using p.step i h
    · by_cases he : i = p.length
      · subst i
        have hn : ¬ p.length+1 ≤ p.length := by omega
        have hq := q.step 0 (by omega)
        simpa [hn, p.last, q.first] using hq
      · have h0 : ¬ i ≤ p.length := by omega
        have h1 : ¬ i+1 ≤ p.length := by omega
        have hadd : i+1-p.length = (i-p.length)+1 := by omega
        simpa only [if_neg h0, if_neg h1, hadd] using q.step (i-p.length) (by omega)

end Route


end Hirsch.CoordinateRoute

namespace Hirsch.HullCoordinate

open Set

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


end Hirsch.HullCoordinate

namespace Hirsch.HullCoordinate

open Set

variable {d : ℕ}

/-- Linear upper bounds extend from the original generators to their entire hull. -/
lemma hull_le (C : Finset (Fin d → ℝ)) (f : (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (M : ℝ) (hC : ∀ x ∈ C, f x ≤ M) :
    ∀ x ∈ convexHull ℝ (C : Set (Fin d → ℝ)), f x ≤ M := by
  apply convexHull_min hC
  intro x hx y hy a b ha hb hab
  change f (a • x+b • y) ≤ M
  simp only [map_add, map_smul, smul_eq_mul]
  calc
    a*f x+b*f y ≤ a*M+b*M := add_le_add
      (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)
    _ = M := by rw [← add_mul, hab, one_mul]

/-- Equality in an upper support bound uses only maximizing generators.
The target K may be any convex set, not a supplied face or edge. -/
lemma hull_support (C : Finset (Fin d → ℝ)) (f : (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (M : ℝ) (K : Set (Fin d → ℝ)) (hK : Convex ℝ K)
    (hC : ∀ x ∈ C, f x ≤ M ∧ (f x=M → x ∈ K)) :
    ∀ x ∈ convexHull ℝ (C : Set (Fin d → ℝ)),
      f x ≤ M ∧ (f x=M → x ∈ K) := by
  apply convexHull_min hC
  intro x hx y hy a b ha hb hab
  change f (a • x+b • y) ≤ M ∧ (f (a • x+b • y)=M → a • x+b • y ∈ K)
  have hval : f (a • x+b • y)=a*f x+b*f y := by
    simp only [map_add, map_smul, smul_eq_mul]
  constructor
  · rw [hval]
    calc
      a*f x+b*f y ≤ a*M+b*M := add_le_add
        (mul_le_mul_of_nonneg_left hx.1 ha) (mul_le_mul_of_nonneg_left hy.1 hb)
      _ = M := by rw [← add_mul, hab, one_mul]
  · intro he
    by_cases ha0 : a=0
    · have hb1 : b=1 := by linarith
      have hyM : f y=M := by simpa [ha0, hb1] using he
      simpa [ha0, hb1] using hy.2 hyM
    by_cases hb0 : b=0
    · have ha1 : a=1 := by linarith
      have hxM : f x=M := by simpa [ha1, hb0] using he
      simpa [ha1, hb0] using hx.2 hxM
    have hsum : a*(M-f x)+b*(M-f y)=0 := by
      calc
        a*(M-f x)+b*(M-f y) = (a+b)*M-(a*f x+b*f y) := by ring
        _ = 0 := by rw [hab, one_mul, ← hval, he, sub_self]
    have hax := mul_nonneg ha (sub_nonneg.mpr hx.1)
    have hby := mul_nonneg hb (sub_nonneg.mpr hy.1)
    have hax0 : a*(M-f x)=0 := by linarith
    have hby0 : b*(M-f y)=0 := by linarith
    have hxM : f x=M :=
      (sub_eq_zero.mp ((mul_eq_zero.mp hax0).resolve_left ha0)).symm
    have hyM : f y=M :=
      (sub_eq_zero.mp ((mul_eq_zero.mp hby0).resolve_left hb0)).symm
    exact hK (hx.2 hxM) (hy.2 hyM) ha hb hab

/-- The strict functional is derived from the requested actual vertex.
This generalizes the finite-corner separation argument used in accepted #316. -/
lemma strict_vertex_functional (C : Finset (Fin d → ℝ)) (u : Fin d → ℝ)
    (hu : u ∈ (convexHull ℝ (C : Set (Fin d → ℝ))).extremePoints ℝ) :
    ∃ h : (Fin d → ℝ) →ₗ[ℝ] ℝ,
      ∀ x ∈ C, x ≠ u → 0 < h (x-u) := by
  classical
  let P := convexHull ℝ (C : Set (Fin d → ℝ))
  have hcv : Convex ℝ P := convex_convexHull ℝ _
  have hremove : Convex ℝ (P \ {u}) :=
    (hcv.mem_extremePoints_iff_convex_diff.mp hu).2
  have hsub : convexHull ℝ ((C : Set (Fin d → ℝ)) \ {u}) ⊆ P \ {u} :=
    convexHull_min (fun x hx => ⟨subset_convexHull ℝ _ hx.1, hx.2⟩) hremove
  have hnot : u ∉ convexHull ℝ ((C : Set (Fin d → ℝ)) \ {u}) := by
    intro h
    exact (hsub h).2 (Set.mem_singleton u)
  have hfinite : ((C : Set (Fin d → ℝ)) \ {u}).Finite :=
    C.finite_toSet.subset Set.diff_subset
  obtain ⟨f, c, hfc, hcu⟩ := geometric_hahn_banach_closed_point
    (convex_convexHull ℝ _) (hfinite.isClosed_convexHull ℝ) hnot
  refine ⟨-f.toLinearMap, ?_⟩
  intro x hx hxu
  have hx' : x ∈ (C : Set (Fin d → ℝ)) \ {u} :=
    ⟨hx, by simpa only [Set.mem_singleton_iff] using hxu⟩
  have hlt : f x < f u := (hfc x (subset_convexHull ℝ _ hx')).trans hcu
  change 0 < -(f.toLinearMap (x-u))
  rw [map_sub]
  change 0 < -(f x-f u)
  linarith

/-- A better feasible value supplies a better original generator. -/
lemma improving_generator (C : Finset (Fin d → ℝ))
    (f : (Fin d → ℝ) →ₗ[ℝ] ℝ) (u y : Fin d → ℝ)
    (hy : y ∈ convexHull ℝ (C : Set (Fin d → ℝ))) (hfy : f u < f y) :
    ∃ x ∈ C, f u < f x := by
  by_contra hn
  have hC : ∀ x ∈ C, f x ≤ f u := by
    intro x hx
    by_contra hh
    exact hn ⟨x, hx, lt_of_not_ge hh⟩
  exact (not_le_of_gt hfy) (hull_le C f (f u) hC y hy)

/-- From an actual vertex and any better feasible point, construct a better
actual vertex joined by a whole nondegenerate ORIGINAL exposed segment.
The finite generator list may contain redundant/interior points. -/
theorem improving_edge (C : Finset (Fin d → ℝ))
    (f : (Fin d → ℝ) →ₗ[ℝ] ℝ) (u y : Fin d → ℝ)
    (hu : u ∈ (convexHull ℝ (C : Set (Fin d → ℝ))).extremePoints ℝ)
    (hy : y ∈ convexHull ℝ (C : Set (Fin d → ℝ))) (hfy : f u < f y) :
    ∃ v ∈ C, v ∈ (convexHull ℝ (C : Set (Fin d → ℝ))).extremePoints ℝ ∧
      f u < f v ∧ u ≠ v ∧
      IsExposed ℝ (convexHull ℝ (C : Set (Fin d → ℝ))) (segment ℝ u v) := by
  classical
  obtain ⟨h, hh⟩ := strict_vertex_functional C u hu
  obtain ⟨a, haC, hfa⟩ := improving_generator C f u y hy hfy
  have hau : a ≠ u := by intro he; rw [he] at hfa; exact (lt_irrefl _) hfa
  let D := C.erase u
  have haD : a ∈ D := Finset.mem_erase.mpr ⟨hau, haC⟩
  have hD : ∀ x ∈ D, 0 < h (x-u) :=
    fun x hx => hh x (Finset.mem_erase.mp hx).2 (Finset.mem_erase.mp hx).1
  let contrast : (Fin d → ℝ) → (Fin d → ℝ) → (Fin d → ℝ) :=
    fun x z => h (x-u) • (z-u)-h (z-u) • (x-u)
  let S := (D.product D).image (fun p => contrast p.1 p.2)
  have hS : ∀ x ∈ D, ∀ z ∈ D, contrast x z ∈ S := by
    intro x hx z hz
    exact Finset.mem_image.mpr ⟨(x,z), Finset.mem_product.mpr ⟨hx,hz⟩, rfl⟩
  obtain ⟨g, hreg, hkeep⟩ := regularize_on S f
  obtain ⟨r, hrD, hrmax⟩ := Finset.exists_max_image D
    (fun x => g (x-u)/h (x-u)) ⟨a,haD⟩
  let M := g (r-u)/h (r-u)
  let q : (Fin d → ℝ) →ₗ[ℝ] ℝ := g-M • h
  have hq : ∀ z, q z=g z-M*h z := by intro z; simp [q, smul_eq_mul]
  have hMr : M*h (r-u)=g (r-u) := div_mul_cancel₀ _ (ne_of_gt (hD r hrD))
  have hqr : q (r-u)=0 := by rw [hq, hMr, sub_self]
  have hbound : ∀ x ∈ D, g (x-u) ≤ M*h (x-u) := by
    intro x hx
    exact (div_le_iff₀ (hD x hx)).mp (hrmax x hx)
  have hqbound : ∀ x ∈ C, q (x-u) ≤ 0 := by
    intro x hx
    by_cases he : x=u
    · simp [he]
    · rw [hq]
      exact sub_nonpos.mpr (hbound x (Finset.mem_erase.mpr ⟨he,hx⟩))
  let T := D.filter (fun x => q (x-u)=0)
  have hrT : r ∈ T := Finset.mem_filter.mpr ⟨hrD,hqr⟩
  obtain ⟨v, hvT, hvmax⟩ := Finset.exists_max_image T (fun x => h (x-u)) ⟨r,hrT⟩
  have hvD : v ∈ D := (Finset.mem_filter.mp hvT).1
  have hvC : v ∈ C := (Finset.mem_erase.mp hvD).2
  have hvu : v ≠ u := (Finset.mem_erase.mp hvD).1
  have hqv : q (v-u)=0 := (Finset.mem_filter.mp hvT).2
  have hgv : g (v-u)=M*h (v-u) := by
    have ht := hqv
    rw [hq] at ht
    exact sub_eq_zero.mp ht
  have hcontrast : ∀ l : (Fin d → ℝ) →ₗ[ℝ] ℝ, ∀ x z,
      l (contrast x z)=h (x-u)*l (z-u)-h (z-u)*l (x-u) := by
    intro l x z
    simp only [contrast, map_sub, map_smul, smul_eq_mul]
  have hfv : f u < f v := by
    have hfa' : 0 < f (a-u) := by rw [map_sub]; exact sub_pos.mpr hfa
    have hfv' : 0 < f (v-u) := by
      by_contra hn
      have hnon : f (v-u) ≤ 0 := le_of_not_gt hn
      have hpos : 0 < f (contrast v a) := by
        rw [hcontrast]
        have hp := mul_pos (hD v hvD) hfa'
        have hn' := mul_nonpos_of_nonneg_of_nonpos (hD a haD).le hnon
        linarith
      have hgpos : 0 < g (contrast v a) :=
        (hkeep _ (hS v hvD a haD) (ne_of_gt hpos)).mpr hpos
      have hgle : g (contrast v a) ≤ 0 := by
        rw [hcontrast, hgv]
        calc
          h (v-u)*g (a-u)-h (a-u)*(M*h (v-u)) ≤
              h (v-u)*(M*h (a-u))-h (a-u)*(M*h (v-u)) :=
            sub_le_sub_right (mul_le_mul_of_nonneg_left (hbound a haD) (hD v hvD).le) _
          _ = 0 := by ring
      exact (not_le_of_gt hgpos) hgle
    rw [map_sub] at hfv'
    exact sub_pos.mp hfv'
  have htied : ∀ x ∈ C, q x=q u → x ∈ segment ℝ u v := by
    intro x hx he
    by_cases hxu : x=u
    · rw [hxu]
      exact left_mem_segment ℝ _ _
    have hxD : x ∈ D := Finset.mem_erase.mpr ⟨hxu,hx⟩
    have hqx : q (x-u)=0 := by rw [map_sub,he,sub_self]
    have hxT : x ∈ T := Finset.mem_filter.mpr ⟨hxD,hqx⟩
    have hgx : g (x-u)=M*h (x-u) := by
      rw [hq] at hqx
      exact sub_eq_zero.mp hqx
    have hgc : g (contrast v x)=0 := by rw [hcontrast,hgx,hgv]; ring
    have hc0 : contrast v x=0 := by
      by_contra hc
      exact hreg _ (hS v hvD x hxD) hc hgc
    have hscaled : h (v-u) • (x-u)=h (x-u) • (v-u) := sub_eq_zero.mp hc0
    let t : ℝ := h (x-u)/h (v-u)
    have ht0 : 0 ≤ t := (div_pos (hD x hxD) (hD v hvD)).le
    have ht1 : t ≤ 1 := (div_le_one (hD v hvD)).mpr (hvmax x hxT)
    have hdiff : x-u=t • (v-u) := by
      calc
        x-u = (h (v-u))⁻¹ • (h (v-u) • (x-u)) := by
          rw [smul_smul, inv_mul_cancel₀ (ne_of_gt (hD v hvD)), one_smul]
        _ = t • (v-u) := by
          rw [hscaled,smul_smul]
          congr 1
          dsimp [t]
          rw [div_eq_mul_inv, mul_comm]
    have hxeq : x=u+t • (v-u) := by rw [← hdiff]; abel
    refine ⟨1-t,t,sub_nonneg.mpr ht1,ht0,by ring,?_⟩
    rw [hxeq]
    module
  have hC : ∀ x ∈ C, q x ≤ q u ∧ (q x=q u → x ∈ segment ℝ u v) := by
    intro x hx
    refine ⟨?_,htied x hx⟩
    have hle := hqbound x hx
    rw [map_sub] at hle
    linarith
  have hsupport := hull_support C q (q u) (segment ℝ u v) (convex_segment u v) hC
  have hvP : v ∈ convexHull ℝ (C : Set (Fin d → ℝ)) := subset_convexHull ℝ _ hvC
  have hqvu : q v=q u := by
    rw [map_sub] at hqv
    exact sub_eq_zero.mp hqv
  have hex : IsExposed ℝ (convexHull ℝ (C : Set (Fin d → ℝ))) (segment ℝ u v) := by
    intro _
    refine ⟨q.toContinuousLinearMap,?_⟩
    ext x
    constructor
    · intro hx
      obtain ⟨a,b,ha,hb,hab,heq⟩ := hx
      have hxP := heq ▸ (convex_convexHull ℝ (C : Set (Fin d → ℝ))) hu.1 hvP ha hb hab
      have hqx : q x=q u := by
        rw [← heq,map_add,map_smul,map_smul,hqvu]
        change a*q u+b*q u=q u
        rw [← add_mul,hab,one_mul]
      refine ⟨hxP,?_⟩
      intro z hz
      change q z ≤ q x
      rw [hqx]
      exact (hsupport z hz).1
    · rintro ⟨hx,hmax⟩
      have hlow := hmax u hu.1
      change q u ≤ q x at hlow
      exact (hsupport x hx).2 (le_antisymm (hsupport x hx).1 hlow)
  have hvext : v ∈ (convexHull ℝ (C : Set (Fin d → ℝ))).extremePoints ℝ := by
    apply hex.isExtreme.extremePoints_subset_extremePoints
    rw [segment_symm]
    exact left_extreme_segment v u hvu
  exact ⟨v,hvC,hvext,hfv,Ne.symm hvu,hex⟩

end Hirsch.HullCoordinate

namespace Hirsch.HullCoordinate

open Set

variable {d : ℕ}

def coordinate (j : Fin d) : (Fin d → ℝ) →ₗ[ℝ] ℝ where
  toFun x := x j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Filtering original generators at an attained linear maximum gives the
entire exposed hull face, not just a subset of its vertices. -/
lemma hull_filter_exposed {ι : Type*} [DecidableEq ι]
    (F : Finset ι) (c : ι → (Fin d → ℝ))
    (f : (Fin d → ℝ) →ₗ[ℝ] ℝ) (a : ι) (ha : a ∈ F)
    (hmax : ∀ x ∈ F, f (c x) ≤ f (c a)) :
    IsExposed ℝ (convexHull ℝ (F.image c : Set (Fin d → ℝ)))
      (convexHull ℝ ((F.filter (fun x => f (c x)=f (c a))).image c : Set (Fin d → ℝ))) := by
  classical
  let T := F.filter (fun x => f (c x)=f (c a))
  let K := convexHull ℝ (T.image c : Set (Fin d → ℝ))
  have hsub : K ⊆ convexHull ℝ (F.image c : Set (Fin d → ℝ)) := by
    apply convexHull_mono
    intro x hx
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_image.mpr ⟨i,(Finset.mem_filter.mp hi).1,rfl⟩
  have hconst : ∀ x ∈ K, f x=f (c a) := by
    apply convexHull_min
    · intro x hx
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
      exact (Finset.mem_filter.mp hi).2
    · intro x hx y hy s t hs ht hst
      change f (s • x+t • y)=f (c a)
      rw [map_add,map_smul,map_smul,hx,hy]
      change s*f (c a)+t*f (c a)=f (c a)
      rw [← add_mul,hst,one_mul]
  have hC : ∀ x ∈ F.image c, f x ≤ f (c a) ∧ (f x=f (c a) → x ∈ K) := by
    intro x hx
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
    refine ⟨hmax i hi,?_⟩
    intro he
    apply subset_convexHull ℝ _
    exact Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨hi,he⟩,rfl⟩
  have hsup := hull_support (F.image c) f (f (c a)) K (convex_convexHull ℝ _) hC
  have haP : c a ∈ convexHull ℝ (F.image c : Set (Fin d → ℝ)) :=
    subset_convexHull ℝ _ (Finset.mem_image.mpr ⟨a,ha,rfl⟩)
  intro _
  refine ⟨f.toContinuousLinearMap,?_⟩
  ext x
  constructor
  · intro hx
    refine ⟨hsub hx,?_⟩
    intro y hy
    change f y ≤ f x
    rw [hconst x hx]
    exact (hsup y hy).1
  · rintro ⟨hx,hmaxx⟩
    have hlo := hmaxx (c a) haP
    change f (c a) ≤ f x at hlo
    exact (hsup x hx).2 (le_antisymm (hsup x hx).1 hlo)


end Hirsch.HullCoordinate

namespace Hirsch.TargetRows

open Set

variable {d m : ℕ}

def body (A : Fin m → (Fin d → ℝ) →ₗ[ℝ] ℝ) (b : Fin m → ℝ) : Set (Fin d → ℝ) :=
  {x | ∀ i, A i x ≤ b i}

noncomputable def active (A : Fin m → (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (b : Fin m → ℝ) (x : Fin d → ℝ) : Finset (Fin m) := by
  classical
  exact Finset.univ.filter (fun i => A i x = b i)

noncomputable def missing (A : Fin m → (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (b : Fin m → ℝ) (v x : Fin d → ℝ) : Finset (Fin m) := by
  classical
  exact Finset.univ.filter (fun i => A i v = b i ∧ A i x ≠ b i)

noncomputable def vertexSet (C : Finset (Fin d → ℝ))
    (A : Fin m → (Fin d → ℝ) →ₗ[ℝ] ℝ) (b : Fin m → ℝ) : Finset (Fin d → ℝ) := by
  classical
  exact C.filter (fun x => x ∈ (body A b).extremePoints ℝ)

@[simp] lemma mem_active (A : Fin m → (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (b : Fin m → ℝ) (x : Fin d → ℝ) (i : Fin m) :
    i ∈ active A b x ↔ A i x = b i := by
  classical
  simp [active]

@[simp] lemma mem_missing (A : Fin m → (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (b : Fin m → ℝ) (v x : Fin d → ℝ) (i : Fin m) :
    i ∈ missing A b v x ↔ A i v = b i ∧ A i x ≠ b i := by
  classical
  simp [missing]

/-- Finite opposite perturbations derive active-row injectivity at an actual
vertex. There is no full-dimensionality, strict-feasibility or basis premise. -/
lemma extreme_kernel (A : Fin m → (Fin d → ℝ) →ₗ[ℝ] ℝ) (b : Fin m → ℝ)
    (x : Fin d → ℝ) (hx : x ∈ (body A b).extremePoints ℝ)
    (z : Fin d → ℝ) (hz : ∀ i, A i x = b i → A i z = 0) : z = 0 := by
  classical
  let S := Finset.univ.filter (fun i : Fin m => A i x ≠ b i)
  have hslack : ∀ i ∈ S, 0 < b i-A i x := by
    intro i hi
    exact sub_pos.mpr (lt_of_le_of_ne (hx.1 i) (Finset.mem_filter.mp hi).2)
  obtain ⟨e,he,hsmall⟩ := HullCoordinate.finite_margin S (fun i => b i-A i x)
    (fun i => A i z) hslack
  have hcuts : ∀ i, A i (x+e•z) ≤ b i ∧ A i (x-e•z) ≤ b i := by
    intro i
    by_cases hi : A i x = b i
    · simp only [map_add,map_sub,map_smul,smul_eq_mul,hz i hi,mul_zero,add_zero,sub_zero]
      exact ⟨hx.1 i,hx.1 i⟩
    · have hs : i ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ i,hi⟩
      have hb := hsmall i hs
      have hlo := mul_le_mul_of_nonneg_left (neg_abs_le (A i z)) he.le
      have hhi := mul_le_mul_of_nonneg_left (le_abs_self (A i z)) he.le
      simp only [map_add,map_sub,map_smul,smul_eq_mul]
      constructor <;> nlinarith
  have hmid : x ∈ openSegment ℝ (x+e•z) (x-e•z) := by
    refine ⟨(1/2 : ℝ),(1/2 : ℝ),by norm_num,by norm_num,by norm_num,?_⟩
    module
  have heq : x+e•z=x := hx.2 (fun i => (hcuts i).1) (fun i => (hcuts i).2) hmid
  funext j
  have h := congrFun heq j
  change x j+e*z j=x j at h
  have hprod : e*z j=0 := by linarith
  exact (mul_eq_zero.mp hprod).resolve_left (ne_of_gt he)

/-- All rows tight at an actual vertex determine that point uniquely. -/
lemma determined_by_active (A : Fin m → (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (b : Fin m → ℝ) (v : Fin d → ℝ) (hv : v ∈ (body A b).extremePoints ℝ)
    (x : Fin d → ℝ) (hx : ∀ i, A i v=b i → A i x=b i) : x=v := by
  apply sub_eq_zero.mp
  apply extreme_kernel A b v hv (x-v)
  intro i hi
  rw [map_sub,hx i hi,hi,sub_self]

/-- At least ambient dimension many original rows are tight at a vertex,
even with redundant rows or a lower-dimensional feasible body. -/
lemma active_card (A : Fin m → (Fin d → ℝ) →ₗ[ℝ] ℝ) (b : Fin m → ℝ)
    (x : Fin d → ℝ) (hx : x ∈ (body A b).extremePoints ℝ) :
    d ≤ (active A b x).card := by
  classical
  let E : (Fin d → ℝ) →ₗ[ℝ] ((active A b x) → ℝ) :=
    { toFun := fun z i => A i.val z
      map_add' := by intro y z; funext i; exact map_add (A i.val) y z
      map_smul' := by intro a z; funext i; exact map_smul (A i.val) a z }
  have hinj : Function.Injective E := by
    intro y z he
    apply sub_eq_zero.mp
    apply extreme_kernel A b x hx (y-z)
    intro i hi
    have h : A i y=A i z := congrFun he ⟨i,(mem_active A b x i).mpr hi⟩
    rw [map_sub,h,sub_self]
  have h := LinearMap.finrank_le_finrank_of_injective hinj
  simpa only [Module.finrank_pi,Module.finrank_self,Fintype.card_fin,Fintype.card_coe] using h

lemma missing_bound (A : Fin m → (Fin d → ℝ) →ₗ[ℝ] ℝ) (b : Fin m → ℝ)
    (u v : Fin d → ℝ) (hu : u ∈ (body A b).extremePoints ℝ) :
    (missing A b v u).card ≤ m-d := by
  classical
  have hd : Disjoint (missing A b v u) (active A b u) := by
    apply Finset.disjoint_left.mpr
    intro i hi ha
    exact ((mem_missing A b v u i).mp hi).2 ((mem_active A b u i).mp ha)
  have hc := Finset.card_le_card (Finset.subset_univ
    (missing A b v u ∪ active A b u))
  rw [Finset.card_union_of_disjoint hd,Finset.card_univ,Fintype.card_fin] at hc
  have hr := active_card A b u hu
  omega

noncomputable def locked (C : Finset (Fin d → ℝ))
    (A : Fin m → (Fin d → ℝ) →ₗ[ℝ] ℝ) (b : Fin m → ℝ)
    (S : Finset (Fin m)) : Finset (Fin d → ℝ) := by
  classical
  exact C.filter (fun x => ∀ i ∈ S, A i x=b i)

/-- Locking any collection of original rows tight at the target retains an
actual original face, with the full finite generator hull proved exactly. -/
lemma locked_face (C : Finset (Fin d → ℝ))
    (A : Fin m → (Fin d → ℝ) →ₗ[ℝ] ℝ) (b : Fin m → ℝ)
    (hP : convexHull ℝ (C : Set (Fin d → ℝ))=body A b)
    (v : Fin d → ℝ) (hvC : v ∈ C) :
    ∀ S : Finset (Fin m), (∀ i ∈ S, A i v=b i) →
      IsExtreme ℝ (body A b)
        (convexHull ℝ (locked C A b S : Set (Fin d → ℝ))) := by
  classical
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro _
    simpa [locked,hP] using (show IsExtreme ℝ (body A b) (body A b) from IsExtreme.rfl)
  | @insert i S hi ih =>
    intro htarget
    have hvi := htarget i (Finset.mem_insert_self i S)
    have hS : ∀ j ∈ S, A j v=b j := fun j hj => htarget j (Finset.mem_insert_of_mem hj)
    let D := locked C A b S
    have hvD : v ∈ D := Finset.mem_filter.mpr ⟨hvC,hS⟩
    have hmax : ∀ x ∈ D, A i x ≤ A i v := by
      intro x hx
      rw [hvi]
      have hxC : x ∈ C := (Finset.mem_filter.mp hx).1
      have hxP : x ∈ body A b := hP ▸ subset_convexHull ℝ _ hxC
      exact hxP i
    have hex := HullCoordinate.hull_filter_exposed D (fun x => x) (A i) v hvD hmax
    have hfilter : D.filter (fun x => A i x=A i v)=locked C A b (insert i S) := by
      ext x
      simp only [D,locked,Finset.mem_filter,Finset.mem_insert]
      constructor
      · rintro ⟨⟨hx,hs⟩,he⟩
        refine ⟨hx,?_⟩
        intro j hj
        rcases hj with hj | hj
        · subst j
          exact he.trans hvi
        · exact hs j hj
      · rintro ⟨hx,hs⟩
        exact ⟨⟨hx,fun j hj => hs j (Or.inr hj)⟩,(hs i (Or.inl rfl)).trans hvi.symm⟩
    have hlocal : IsExtreme ℝ (convexHull ℝ (D : Set (Fin d → ℝ)))
        (convexHull ℝ (D.filter (fun x => A i x=A i v) : Set (Fin d → ℝ))) := by
      have hid : ∀ E : Finset (Fin d → ℝ), E.image (fun x => x)=E := by
        intro E
        ext x
        constructor
        · intro hx
          obtain ⟨y,hy,he⟩ := Finset.mem_image.mp hx
          exact he ▸ hy
        · intro hx
          exact Finset.mem_image.mpr ⟨x,hx,rfl⟩
      simpa only [hid] using hex.isExtreme
    rw [hfilter] at hlocal
    exact (ih hS).trans hlocal

end Hirsch.TargetRows

namespace Hirsch.FewExceptions

open Set TargetRows

variable {d m : ℕ}

/-- Original edges which preserve every target row acquired so far. -/
def Edge (A : Fin m → (Fin d → ℝ) →ₗ[ℝ] ℝ) (b : Fin m → ℝ)
    (v x y : Fin d → ℝ) : Prop :=
  x ≠ y ∧ IsExtreme ℝ (body A b) (segment ℝ x y) ∧
    ∀ i, A i v=b i → A i x=b i → A i y=b i

/-- A better linear value supplies an original edge in the retained target face.
No two-level, neighbor or dimension hypothesis is used in this helper. -/
lemma improve_locked (C : Finset (Fin d → ℝ))
    (A : Fin m → (Fin d → ℝ) →ₗ[ℝ] ℝ) (b : Fin m → ℝ)
    (hP : convexHull ℝ (C : Set (Fin d → ℝ))=body A b)
    (v : Fin d → ℝ) (hv : v ∈ (body A b).extremePoints ℝ)
    (x : Fin d → ℝ) (hx : x ∈ (body A b).extremePoints ℝ)
    (f : (Fin d → ℝ) →ₗ[ℝ] ℝ) (hf : f x < f v) :
    ∃ y ∈ (body A b).extremePoints ℝ, Edge A b v x y ∧ f x < f y := by
  classical
  have hxC : x ∈ C := extremePoints_convexHull_subset (hP.symm ▸ hx)
  have hvC : v ∈ C := extremePoints_convexHull_subset (hP.symm ▸ hv)
  let S := active A b x ∩ active A b v
  let D := locked C A b S
  have htarget : ∀ i ∈ S, A i v=b i := by
    intro i hi
    exact (mem_active A b v i).mp (Finset.mem_inter.mp hi).2
  have hsource : ∀ i ∈ S, A i x=b i := by
    intro i hi
    exact (mem_active A b x i).mp (Finset.mem_inter.mp hi).1
  have hface := locked_face C A b hP v hvC S htarget
  have hxD : x ∈ D := Finset.mem_filter.mpr ⟨hxC,hsource⟩
  have hvD : v ∈ D := Finset.mem_filter.mpr ⟨hvC,htarget⟩
  have hxK : x ∈ convexHull ℝ (D : Set (Fin d → ℝ)) := subset_convexHull ℝ _ hxD
  have hvK : v ∈ convexHull ℝ (D : Set (Fin d → ℝ)) := subset_convexHull ℝ _ hvD
  have hxE : x ∈ (convexHull ℝ (D : Set (Fin d → ℝ))).extremePoints ℝ :=
    inter_extremePoints_subset_extremePoints_of_subset hface.subset ⟨hxK,hx⟩
  obtain ⟨y,hyD,hyE,hinc,hxy,hseg⟩ := HullCoordinate.improving_edge D f x v hxE hvK hf
  have hy : y ∈ (body A b).extremePoints ℝ := hface.extremePoints_subset_extremePoints hyE
  refine ⟨y,hy,⟨hxy,hface.trans hseg.isExtreme,?_⟩,hinc⟩
  intro i hiv hix
  have hi : i ∈ S := Finset.mem_inter.mpr
    ⟨(mem_active A b x i).mpr hix,(mem_active A b v i).mpr hiv⟩
  exact (Finset.mem_filter.mp hyD).2 i hi

noncomputable def good (A : Fin m → (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (b : Fin m → ℝ) (v : Fin d → ℝ) (B : Finset (Fin m)) : Finset (Fin m) :=
  active A b v \ B

noncomputable def todo (A : Fin m → (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (b : Fin m → ℝ) (v : Fin d → ℝ) (B : Finset (Fin m))
    (x : Fin d → ℝ) : Finset (Fin m) := by
  classical
  exact (good A b v B).filter (fun i => A i x ≠ b i)

noncomputable def residual (C : Finset (Fin d → ℝ))
    (A : Fin m → (Fin d → ℝ) →ₗ[ℝ] ℝ) (b : Fin m → ℝ)
    (v : Fin d → ℝ) (B : Finset (Fin m)) : Finset (Fin d → ℝ) := by
  classical
  exact (vertexSet C A b).filter (fun x => ∀ i ∈ good A b v B, A i x=b i)

/-- The direction space after all nonexceptional target equations are fixed. -/
def directions (A : Fin m → (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (G : Finset (Fin m)) : Submodule ℝ (Fin d → ℝ) where
  carrier := {z | ∀ i ∈ G, A i z=0}
  zero_mem' := by intro i hi; exact map_zero (A i)
  add_mem' := by
    intro x y hx hy i hi
    rw [map_add,hx i hi,hy i hi,add_zero]
  smul_mem' := by
    intro a x hx i hi
    rw [map_smul,hx i hi,smul_zero]

/-- Target-active injectivity bounds residual dimension by the NUMBER of
exceptional labels, not by their real vertex-value inventories. -/
theorem residual_dimension (A : Fin m → (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (b : Fin m → ℝ) (v : Fin d → ℝ)
    (hv : v ∈ (body A b).extremePoints ℝ) (B : Finset (Fin m)) :
    Module.finrank ℝ (directions A (good A b v B)) ≤ B.card := by
  classical
  let N := directions A (good A b v B)
  let E : N →ₗ[ℝ] (B → ℝ) :=
    { toFun := fun z i => A i.val z.val
      map_add' := by intro x y; funext i; exact map_add (A i.val) x.val y.val
      map_smul' := by intro a x; funext i; exact map_smul (A i.val) a x.val }
  have hE : Function.Injective E := by
    intro x y he
    apply Subtype.ext
    apply sub_eq_zero.mp
    apply extreme_kernel A b v hv (x.val-y.val)
    intro i hi
    by_cases hiB : i ∈ B
    · have h : A i x.val=A i y.val := congrFun he ⟨i,hiB⟩
      rw [map_sub,h,sub_self]
    · have hiG : i ∈ good A b v B :=
        Finset.mem_sdiff.mpr ⟨(mem_active A b v i).mpr hi,hiB⟩
      rw [map_sub,x.property i hiG,y.property i hiG,sub_self]
  have h := LinearMap.finrank_le_finrank_of_injective hE
  simpa only [Module.finrank_pi,Module.finrank_self,Fintype.card_coe] using h

/-- Acquire all good target rows. Each original edge consumes a new good label,
while even already acquired exceptional rows stay locked. -/
theorem enter_residual (C : Finset (Fin d → ℝ))
    (A : Fin m → (Fin d → ℝ) →ₗ[ℝ] ℝ) (b : Fin m → ℝ)
    (hP : convexHull ℝ (C : Set (Fin d → ℝ))=body A b)
    (v : Fin d → ℝ) (hv : v ∈ (body A b).extremePoints ℝ)
    (B : Finset (Fin m))
    (htwo : ∀ i, i ∉ B → A i v=b i → ∃ lo : ℝ,
      ∀ x ∈ (body A b).extremePoints ℝ, A i x=lo ∨ A i x=b i)
    (u : Fin d → ℝ) (hu : u ∈ (body A b).extremePoints ℝ) :
    ∃ w ∈ residual C A b v B,
      ∃ p : CoordinateRoute.Route (Edge A b v) (vertexSet C A b) u w,
        p.length ≤ (todo A b v B u).card := by
  classical
  have hmem : ∀ x ∈ (body A b).extremePoints ℝ, x ∈ vertexSet C A b := by
    intro x hx
    exact Finset.mem_filter.mpr ⟨extremePoints_convexHull_subset (hP.symm ▸ hx),hx⟩
  have aux : ∀ k : ℕ, ∀ x : Fin d → ℝ, x ∈ (body A b).extremePoints ℝ →
      (todo A b v B x).card=k →
      ∃ w ∈ residual C A b v B,
        ∃ p : CoordinateRoute.Route (Edge A b v) (vertexSet C A b) x w,
          p.length ≤ (todo A b v B x).card := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro x hx hk
      by_cases hdone : ∀ i ∈ good A b v B, A i x=b i
      · exact ⟨x,Finset.mem_filter.mpr ⟨hmem x hx,hdone⟩,
          CoordinateRoute.Route.nil (hmem x hx),by simp [CoordinateRoute.Route.nil]⟩
      have hsome : ∃ j ∈ good A b v B, A j x ≠ b j := by
        by_contra hn
        apply hdone
        intro j hj
        by_contra he
        exact hn ⟨j,hj,he⟩
      obtain ⟨j,hj,hjx⟩ := hsome
      have hjv : A j v=b j := (mem_active A b v j).mp (Finset.mem_sdiff.mp hj).1
      have hjB : j ∉ B := (Finset.mem_sdiff.mp hj).2
      have hjlt : A j x < A j v := by rw [hjv]; exact lt_of_le_of_ne (hx.1 j) hjx
      obtain ⟨y,hy,hedge,hinc⟩ := improve_locked C A b hP v hv x hx (A j) hjlt
      obtain ⟨lo,hlo⟩ := htwo j hjB hjv
      have hjy : A j y=b j := by
        rcases hlo x hx with hxL | hxT
        · rcases hlo y hy with hyL | hyT
          · rw [hxL,hyL] at hinc
            exact False.elim ((lt_irrefl lo) hinc)
          · exact hyT
        · exact False.elim (hjx hxT)
      have hdec : (todo A b v B y).card < (todo A b v B x).card := by
        apply Finset.card_lt_card
        refine Finset.ssubset_iff_subset_ne.mpr ⟨?_,?_⟩
        · intro i hi
          obtain ⟨hiG,hiy⟩ := Finset.mem_filter.mp hi
          have hiv : A i v=b i := (mem_active A b v i).mp (Finset.mem_sdiff.mp hiG).1
          exact Finset.mem_filter.mpr ⟨hiG,fun hix => hiy (hedge.2.2 i hiv hix)⟩
        · intro he
          have hm : j ∈ todo A b v B y := by
            rw [he]
            exact Finset.mem_filter.mpr ⟨hj,hjx⟩
          exact (Finset.mem_filter.mp hm).2 hjy
      obtain ⟨w,hw,p,hp⟩ := ih (todo A b v B y).card (by omega) y hy rfl
      refine ⟨w,hw,CoordinateRoute.Route.prepend (hmem x hx) hedge p,?_⟩
      change p.length+1 ≤ (todo A b v B x).card
      omega
  exact aux (todo A b v B u).card u hu rfl

/-- Finite strict progress constructs a path; the number of larger vertices
is a derived decreasing measure, not an assumed path-length bound. -/
lemma finite_ascent {α : Type*} [DecidableEq α]
    (D : Finset α) (R : α → α → Prop) (f : α → ℝ) (v : α)
    (hstep : ∀ x ∈ D, x ≠ v → ∃ y ∈ D, R x y ∧ f x < f y)
    (u : α) (hu : u ∈ D) :
    ∃ p : CoordinateRoute.Route R D u v, p.length+1 ≤ D.card := by
  classical
  let above : α → Finset α := fun x => D.filter (fun y => f x < f y)
  have aux : ∀ k : ℕ, ∀ x : α, x ∈ D → (above x).card=k →
      ∃ p : CoordinateRoute.Route R D x v, p.length ≤ (above x).card := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro x hx hk
      by_cases he : x=v
      · subst x
        exact ⟨CoordinateRoute.Route.nil hx,by simp [CoordinateRoute.Route.nil]⟩
      obtain ⟨y,hy,hxy,hinc⟩ := hstep x hx he
      have hdec : (above y).card < (above x).card := by
        apply Finset.card_lt_card
        refine Finset.ssubset_iff_subset_ne.mpr ⟨?_,?_⟩
        · intro z hz
          exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hz).1,
            hinc.trans (Finset.mem_filter.mp hz).2⟩
        · intro heq
          have hym : y ∈ above x := Finset.mem_filter.mpr ⟨hy,hinc⟩
          rw [← heq] at hym
          exact (lt_irrefl (f y)) (Finset.mem_filter.mp hym).2
      obtain ⟨p,hp⟩ := ih (above y).card (by omega) y hy rfl
      refine ⟨CoordinateRoute.Route.prepend hx hxy p,?_⟩
      change p.length+1 ≤ (above x).card
      omega
  obtain ⟨p,hp⟩ := aux (above u).card u hu rfl
  have hbound : (above u).card < D.card := by
    apply Finset.card_lt_card
    refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _,?_⟩
    intro he
    have hm : u ∈ above u := by rw [he]; exact hu
    exact (lt_irrefl (f u)) (Finset.mem_filter.mp hm).2
  exact ⟨p,by omega⟩

end Hirsch.FewExceptions

namespace Hirsch.PlanarResidual

open Set TargetRows FewExceptions

variable {d m : ℕ}

/-- An affine image of a space of dimension at most one contains at most two
extreme points of any ambient set. No ordered vertex catalogue is assumed. -/
lemma line_extreme_card {W : Type*} [AddCommGroup W] [Module ℝ W]
    [FiniteDimensional ℝ W] (e : W →ₗ[ℝ] (Fin d → ℝ))
    (hW : Module.finrank ℝ W ≤ 1) (P : Set (Fin d → ℝ))
    (V : Finset (Fin d → ℝ)) (hV : ∀ x ∈ V, x ∈ P.extremePoints ℝ)
    (hdiff : ∀ x ∈ V, ∀ y ∈ V, ∃ z : W, e z=x-y) : V.card ≤ 2 := by
  classical
  by_cases hne : V.Nonempty
  · obtain ⟨a,ha⟩ := hne
    obtain ⟨D,hD⟩ := (finrank_le_one_iff (K := ℝ) (V := W)).mp hW
    have hparam : ∀ x : V, ∃ t : ℝ, x.val=a+t • e D := by
      intro x
      obtain ⟨z,hz⟩ := hdiff x.val x.property a ha
      obtain ⟨t,ht⟩ := hD z
      refine ⟨t,?_⟩
      have he : t • e D=x.val-a := by rw [← map_smul,ht,hz]
      rw [he]
      abel
    choose t ht using hparam
    obtain ⟨u,_,hmin⟩ := Finset.exists_min_image (Finset.univ : Finset V) t
      ⟨⟨a,ha⟩,Finset.mem_univ _⟩
    obtain ⟨v,_,hmax⟩ := Finset.exists_max_image (Finset.univ : Finset V) t
      ⟨⟨a,ha⟩,Finset.mem_univ _⟩
    have hsub : V ⊆ {u.val,v.val} := by
      intro x hx
      let z : V := ⟨x,hx⟩
      by_cases hxu : x=u.val
      · simp only [Finset.mem_insert,Finset.mem_singleton]
        exact Or.inl hxu
      by_cases hxv : x=v.val
      · simp only [Finset.mem_insert,Finset.mem_singleton]
        exact Or.inr hxv
      have htu : t u < t z := by
        apply lt_of_le_of_ne (hmin z (Finset.mem_univ _))
        intro he
        apply hxu
        change z.val=u.val
        rw [ht z,ht u,he]
      have htv : t z < t v := by
        apply lt_of_le_of_ne (hmax z (Finset.mem_univ _))
        intro he
        apply hxv
        change z.val=v.val
        rw [ht z,ht v,he]
      have hden : 0 < t v-t u := sub_pos.mpr (htu.trans htv)
      let s : ℝ := (t z-t u)/(t v-t u)
      have hs0 : 0 < s := div_pos (sub_pos.mpr htu) hden
      have hs1 : s < 1 := (div_lt_one hden).mpr (by linarith)
      have hmul : s*(t v-t u)=t z-t u := div_mul_cancel₀ _ (ne_of_gt hden)
      have hweight : (1-s)*t u+s*t v=t z := by nlinarith
      have hseg : x ∈ openSegment ℝ u.val v.val := by
        refine ⟨1-s,s,sub_pos.mpr hs1,hs0,by ring,?_⟩
        change (1-s) • u.val+s • v.val=z.val
        rw [ht u,ht v,ht z]
        calc
          (1-s) • (a+t u • e D)+s • (a+t v • e D) =
              a+((1-s)*t u+s*t v) • e D := by module
          _ = a+t z • e D := by rw [hweight]
      have he : u.val=x := (hV x hx).2 (hV u.val u.property).1
        (hV v.val v.property).1 hseg
      exact False.elim (hxu he.symm)
    exact (Finset.card_le_card hsub).trans
      ((Finset.card_insert_le _ _).trans (by simp))
  · have he : V=∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    simp [he]

noncomputable def nonzeroActive (A : Fin m → (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (b : Fin m → ℝ) (N : Submodule ℝ (Fin d → ℝ))
    (x : Fin d → ℝ) : Finset (Fin m) := by
  classical
  exact Finset.univ.filter (fun i => A i x=b i ∧ (A i).comp N.subtype ≠ 0)

/-- Only nonzero row restrictions count. The active-kernel theorem derives
at least dim(N) such ORIGINAL incidences at every actual vertex. -/
lemma active_nonzero_card (A : Fin m → (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (b : Fin m → ℝ) (N : Submodule ℝ (Fin d → ℝ))
    (x : Fin d → ℝ) (hx : x ∈ (body A b).extremePoints ℝ) :
    Module.finrank ℝ N ≤ (nonzeroActive A b N x).card := by
  classical
  let I := nonzeroActive A b N x
  let E : N →ₗ[ℝ] (I → ℝ) :=
    { toFun := fun z i => A i.val z.val
      map_add' := by intro y z; funext i; exact map_add (A i.val) y.val z.val
      map_smul' := by intro a z; funext i; exact map_smul (A i.val) a z.val }
  have hinj : Function.Injective E := by
    intro y z he
    apply Subtype.ext
    apply sub_eq_zero.mp
    apply extreme_kernel A b x hx (y.val-z.val)
    intro i hi
    by_cases hz : (A i).comp N.subtype=0
    · have h : ((A i).comp N.subtype) (y-z)=0 := by rw [hz]; rfl
      exact h
    · have hiI : i ∈ I := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi,hz⟩
      have h : A i y.val=A i z.val := congrFun he ⟨i,hiI⟩
      rw [map_sub,h,sub_self]
  have h := LinearMap.finrank_le_finrank_of_injective hinj
  simpa only [Module.finrank_pi,Module.finrank_self,Fintype.card_coe] using h

/-- In a residual plane, a row with nonzero restriction has an affine line as
its equality slice. At most two actual extreme points lie on that slice. -/
lemma row_slice_card (A : Fin m → (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (b : Fin m → ℝ) (N : Submodule ℝ (Fin d → ℝ))
    (hN : Module.finrank ℝ N ≤ 2)
    (V : Finset (Fin d → ℝ)) (hV : ∀ x ∈ V, x ∈ (body A b).extremePoints ℝ)
    (hdiff : ∀ x ∈ V, ∀ y ∈ V, x-y ∈ N)
    (i : Fin m) (hi : (A i).comp N.subtype ≠ 0) :
    (V.filter (fun x => A i x=b i)).card ≤ 2 := by
  classical
  let f := (A i).comp N.subtype
  have hproper : LinearMap.ker f ≠ ⊤ := by
    intro he
    apply hi
    ext z
    have hz : z ∈ LinearMap.ker f := by rw [he]; exact Submodule.mem_top
    exact hz
  have hlt := Submodule.finrank_lt hproper
  have hker : Module.finrank ℝ (LinearMap.ker f) ≤ 1 := by omega
  let e : (LinearMap.ker f) →ₗ[ℝ] (Fin d → ℝ) :=
    N.subtype.comp (LinearMap.ker f).subtype
  apply line_extreme_card (W := LinearMap.ker f) e hker (body A b) _
  · intro x hx
    exact hV x (Finset.mem_filter.mp hx).1
  · intro x hx y hy
    have hx' := Finset.mem_filter.mp hx
    have hy' := Finset.mem_filter.mp hy
    let z : N := ⟨x-y,hdiff x hx'.1 y hy'.1⟩
    have hz : z ∈ LinearMap.ker f := by
      change A i (x-y)=0
      rw [map_sub,hx'.2,hy'.2,sub_self]
    exact ⟨⟨z,hz⟩,rfl⟩

/-- Double-count actual vertex/original-row incidences, not possible bases.
Zero row restrictions are excluded on BOTH sides of the count. -/
theorem planar_vertex_card (A : Fin m → (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (b : Fin m → ℝ) (N : Submodule ℝ (Fin d → ℝ))
    (hN : Module.finrank ℝ N ≤ 2)
    (V : Finset (Fin d → ℝ)) (hV : ∀ x ∈ V, x ∈ (body A b).extremePoints ℝ)
    (hdiff : ∀ x ∈ V, ∀ y ∈ V, x-y ∈ N) : V.card ≤ m+1 := by
  classical
  by_cases hm : m=0
  · have hcard : V.card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro x hx y hy
      apply sub_eq_zero.mp
      apply extreme_kernel A b x (hV x hx) (x-y)
      intro i hi
      have hib := i.isLt
      omega
    omega
  by_cases hsmall : Module.finrank ℝ N ≤ 1
  · have hc : V.card ≤ 2 := by
      apply line_extreme_card N.subtype hsmall (body A b) V hV
      intro x hx y hy
      exact ⟨⟨x-y,hdiff x hx y hy⟩,rfl⟩
    omega
  have hdim : Module.finrank ℝ N=2 := by omega
  let I := Finset.univ.filter (fun i : Fin m => (A i).comp N.subtype ≠ 0)
  have hlower : ∀ x ∈ V, 2 ≤ (I.filter (fun i => A i x=b i)).card := by
    intro x hx
    have h := active_nonzero_card A b N x (hV x hx)
    rw [hdim] at h
    have he : I.filter (fun i => A i x=b i)=nonzeroActive A b N x := by
      ext i
      simp only [I,nonzeroActive,Finset.mem_filter,Finset.mem_univ,true_and,and_comm]
    rw [he]
    exact h
  have hdouble : (∑ x ∈ V, (I.filter (fun i => A i x=b i)).card)=
      ∑ i ∈ I, (V.filter (fun x => A i x=b i)).card := by
    simp only [Finset.card_eq_sum_ones,Finset.sum_filter]
    rw [Finset.sum_comm]
  have hcount : 2*V.card ≤ 2*I.card := by
    calc
      2*V.card = ∑ _x ∈ V, 2 := by simp [Nat.mul_comm]
      _ ≤ ∑ x ∈ V, (I.filter (fun i => A i x=b i)).card :=
        Finset.sum_le_sum (fun x hx => hlower x hx)
      _ = ∑ i ∈ I, (V.filter (fun x => A i x=b i)).card := hdouble
      _ ≤ ∑ _i ∈ I, 2 := by
        apply Finset.sum_le_sum
        intro i hi
        exact row_slice_card A b N hN V hV hdiff i (Finset.mem_filter.mp hi).2
      _ = 2*I.card := by simp [Nat.mul_comm]
  have hI : I.card ≤ m := by
    simpa only [Finset.card_univ,Fintype.card_fin] using
      Finset.card_le_card (Finset.subset_univ I)
  omega

/-- Two exceptional labels force the residual plane geometrically, and its
actual vertex count is linear in the original row count. -/
theorem residual_card_linear (C : Finset (Fin d → ℝ))
    (A : Fin m → (Fin d → ℝ) →ₗ[ℝ] ℝ) (b : Fin m → ℝ)
    (v : Fin d → ℝ) (hv : v ∈ (body A b).extremePoints ℝ)
    (B : Finset (Fin m)) (hB : B.card ≤ 2) :
    (residual C A b v B).card ≤ m+1 := by
  classical
  let V := residual C A b v B
  let N := directions A (good A b v B)
  have hV : ∀ x ∈ V, x ∈ (body A b).extremePoints ℝ := by
    intro x hx
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).2
  have hdiff : ∀ x ∈ V, ∀ y ∈ V, x-y ∈ N := by
    intro x hx y hy i hi
    rw [map_sub,(Finset.mem_filter.mp hx).2 i hi,
      (Finset.mem_filter.mp hy).2 i hi,sub_self]
  exact planar_vertex_card A b N ((residual_dimension A b v hv B).trans hB) V hV hdiff

/-- Reuse the accepted strict-ascent geometry with the new incidence bound.
No graph or short residual walk is supplied as a hypothesis. -/
theorem residual_route_linear (C : Finset (Fin d → ℝ))
    (A : Fin m → (Fin d → ℝ) →ₗ[ℝ] ℝ) (b : Fin m → ℝ)
    (hP : convexHull ℝ (C : Set (Fin d → ℝ))=body A b)
    (v : Fin d → ℝ) (hv : v ∈ (body A b).extremePoints ℝ)
    (B : Finset (Fin m)) (hB : B.card ≤ 2)
    (u : Fin d → ℝ) (hu : u ∈ residual C A b v B) :
    ∃ p : CoordinateRoute.Route (Edge A b v) (residual C A b v B) u v,
      p.length ≤ m := by
  classical
  let D := residual C A b v B
  obtain ⟨h,hh⟩ := HullCoordinate.strict_vertex_functional C v (hP.symm ▸ hv)
  let f : (Fin d → ℝ) →ₗ[ℝ] ℝ := -h
  have hstep : ∀ x ∈ D, x ≠ v → ∃ y ∈ D, Edge A b v x y ∧ f x < f y := by
    intro x hx hne
    have hxV := (Finset.mem_filter.mp hx).1
    have hxC : x ∈ C := (Finset.mem_filter.mp hxV).1
    have hxE : x ∈ (body A b).extremePoints ℝ := (Finset.mem_filter.mp hxV).2
    have hxG := (Finset.mem_filter.mp hx).2
    have hfx : f x < f v := by
      have ht := hh x hxC hne
      rw [map_sub] at ht
      change -h x < -h v
      linarith
    obtain ⟨y,hy,he,hinc⟩ := improve_locked C A b hP v hv x hxE f hfx
    have hyV : y ∈ vertexSet C A b :=
      Finset.mem_filter.mpr ⟨extremePoints_convexHull_subset (hP.symm ▸ hy),hy⟩
    have hyG : ∀ i ∈ good A b v B, A i y=b i := by
      intro i hi
      exact he.2.2 i ((mem_active A b v i).mp (Finset.mem_sdiff.mp hi).1) (hxG i hi)
    exact ⟨y,Finset.mem_filter.mpr ⟨hyV,hyG⟩,he,hinc⟩
  obtain ⟨p,hp⟩ := finite_ascent D (Edge A b v) f v hstep u hu
  have hc : D.card ≤ m+1 := residual_card_linear C A b v hv B hB
  exact ⟨p,by omega⟩

/-- At most two unrestricted target rows have a LINEAR original-m bound,
not the quadratic optional-row-code specialization of the general theorem. -/
theorem two_exception_routes (C : Finset (Fin d → ℝ))
    (A : Fin m → (Fin d → ℝ) →ₗ[ℝ] ℝ) (b : Fin m → ℝ)
    (hP : convexHull ℝ (C : Set (Fin d → ℝ))=body A b)
    (v : Fin d → ℝ) (hv : v ∈ (body A b).extremePoints ℝ)
    (B : Finset (Fin m)) (hB : B.card ≤ 2)
    (htwo : ∀ i, i ∉ B → A i v=b i → ∃ lo : ℝ,
      ∀ x ∈ (body A b).extremePoints ℝ, A i x=lo ∨ A i x=b i)
    (u : Fin d → ℝ) (hu : u ∈ (body A b).extremePoints ℝ) :
    ∃ p : CoordinateRoute.Route (Edge A b v) (vertexSet C A b) u v,
      p.length ≤ (m-d)+m := by
  classical
  obtain ⟨w,hw,p,hp⟩ := enter_residual C A b hP v hv B htwo u hu
  obtain ⟨q,hq⟩ := residual_route_linear C A b hP v hv B hB w hw
  have hsub : residual C A b v B ⊆ vertexSet C A b := Finset.filter_subset _ _
  have ht : todo A b v B u ⊆ missing A b v u := by
    intro i hi
    obtain ⟨hiG,hiu⟩ := Finset.mem_filter.mp hi
    exact (mem_missing A b v u i).mpr
      ⟨(mem_active A b v i).mp (Finset.mem_sdiff.mp hiG).1,hiu⟩
  have hcost := (Finset.card_le_card ht).trans (missing_bound A b u v hu)
  refine ⟨p.append (q.mono hsub),?_⟩
  change p.length+q.length ≤ (m-d)+m
  omega

end Hirsch.PlanarResidual

namespace Hirsch.SpatialResidual

open Set TargetRows FewExceptions PlanarResidual

variable {d m : ℕ}

/-- Transport a three-dimensional nonzero row slice to an AMBIENT planar
subspace, then apply the accepted original-row planar count. -/
lemma spatial_row_slice_card (A : Fin m → (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (b : Fin m → ℝ) (N : Submodule ℝ (Fin d → ℝ))
    (hN : Module.finrank ℝ N ≤ 3)
    (V : Finset (Fin d → ℝ)) (hV : ∀ x ∈ V, x ∈ (body A b).extremePoints ℝ)
    (hdiff : ∀ x ∈ V, ∀ y ∈ V, x-y ∈ N)
    (i : Fin m) (hi : (A i).comp N.subtype ≠ 0) :
    (V.filter (fun x => A i x=b i)).card ≤ m+1 := by
  classical
  let f : N →ₗ[ℝ] ℝ := (A i).comp N.subtype
  have hproper : LinearMap.ker f ≠ ⊤ := by
    intro he
    apply hi
    ext z
    have hz : z ∈ LinearMap.ker f := by rw [he]; exact Submodule.mem_top
    exact hz
  have hlt := Submodule.finrank_lt hproper
  have hker : Module.finrank ℝ (LinearMap.ker f) ≤ 2 := by omega
  let M : Submodule ℝ (Fin d → ℝ) := N ⊓ LinearMap.ker (A i)
  let E : M →ₗ[ℝ] (LinearMap.ker f) :=
    { toFun := fun z => ⟨⟨z.val,z.property.1⟩,by
        change A i z.val=0
        exact z.property.2⟩
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have hE : Function.Injective E := by
    intro x y he
    apply Subtype.ext
    exact congrArg (fun z : LinearMap.ker f => z.val.val) he
  have hM : Module.finrank ℝ M ≤ 2 :=
    (LinearMap.finrank_le_finrank_of_injective hE).trans hker
  apply planar_vertex_card A b M hM _
  · intro x hx
    exact hV x (Finset.mem_filter.mp hx).1
  · intro x hx y hy
    have hx' := Finset.mem_filter.mp hx
    have hy' := Finset.mem_filter.mp hy
    change x-y ∈ N ∧ A i (x-y)=0
    refine ⟨hdiff x hx'.1 y hy'.1,?_⟩
    rw [map_sub,hx'.2,hy'.2,sub_self]

/-- A finite family of actual vertices with at most three independent motions
has a quadratic bound in the ORIGINAL rows; no small catalogue is assumed. -/
theorem spatial_vertex_card (A : Fin m → (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (b : Fin m → ℝ) (N : Submodule ℝ (Fin d → ℝ))
    (hN : Module.finrank ℝ N ≤ 3)
    (V : Finset (Fin d → ℝ)) (hV : ∀ x ∈ V, x ∈ (body A b).extremePoints ℝ)
    (hdiff : ∀ x ∈ V, ∀ y ∈ V, x-y ∈ N) : V.card ≤ m*m+1 := by
  classical
  have hself : m ≤ m*m := by
    by_cases hm : m=0
    · simp [hm]
    · have hm1 : 1 ≤ m := by omega
      simpa using Nat.mul_le_mul_left m hm1
  by_cases hsmall : Module.finrank ℝ N ≤ 2
  · have hc := planar_vertex_card A b N hsmall V hV hdiff
    omega
  have hdim : Module.finrank ℝ N=3 := by omega
  let I := Finset.univ.filter (fun i : Fin m => (A i).comp N.subtype ≠ 0)
  have hlower : ∀ x ∈ V, 3 ≤ (I.filter (fun i => A i x=b i)).card := by
    intro x hx
    have h := active_nonzero_card A b N x (hV x hx)
    rw [hdim] at h
    have he : I.filter (fun i => A i x=b i)=nonzeroActive A b N x := by
      ext i
      simp only [I,nonzeroActive,Finset.mem_filter,Finset.mem_univ,true_and,and_comm]
    rw [he]
    exact h
  have hdouble : (∑ x ∈ V, (I.filter (fun i => A i x=b i)).card)=
      ∑ i ∈ I, (V.filter (fun x => A i x=b i)).card := by
    simp only [Finset.card_eq_sum_ones,Finset.sum_filter]
    rw [Finset.sum_comm]
  have hI : I.card ≤ m := by
    simpa only [Finset.card_univ,Fintype.card_fin] using
      Finset.card_le_card (Finset.subset_univ I)
  have hcount : 3*V.card ≤ m*(m+1) := by
    calc
      3*V.card = ∑ _x ∈ V, 3 := by simp [Nat.mul_comm]
      _ ≤ ∑ x ∈ V, (I.filter (fun i => A i x=b i)).card :=
        Finset.sum_le_sum (fun x hx => hlower x hx)
      _ = ∑ i ∈ I, (V.filter (fun x => A i x=b i)).card := hdouble
      _ ≤ ∑ _i ∈ I, (m+1) := by
        apply Finset.sum_le_sum
        intro i hi
        exact spatial_row_slice_card A b N hN V hV hdiff i (Finset.mem_filter.mp hi).2
      _ = (m+1)*I.card := by simp [Nat.mul_comm]
      _ ≤ (m+1)*m := Nat.mul_le_mul_left (m+1) hI
      _ = m*(m+1) := by ring
  nlinarith

/-- Residual dimension is DERIVED from at most three exceptional target labels. -/
theorem residual_card_quadratic (C : Finset (Fin d → ℝ))
    (A : Fin m → (Fin d → ℝ) →ₗ[ℝ] ℝ) (b : Fin m → ℝ)
    (v : Fin d → ℝ) (hv : v ∈ (body A b).extremePoints ℝ)
    (B : Finset (Fin m)) (hB : B.card ≤ 3) :
    (residual C A b v B).card ≤ m*m+1 := by
  classical
  let V := residual C A b v B
  let N := directions A (good A b v B)
  have hV : ∀ x ∈ V, x ∈ (body A b).extremePoints ℝ := by
    intro x hx
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).2
  have hdiff : ∀ x ∈ V, ∀ y ∈ V, x-y ∈ N := by
    intro x hx y hy i hi
    rw [map_sub,(Finset.mem_filter.mp hx).2 i hi,
      (Finset.mem_filter.mp hy).2 i hi,sub_self]
  exact spatial_vertex_card A b N ((residual_dimension A b v hv B).trans hB) V hV hdiff

/-- Construct the locked suffix from genuine improving edges and the derived
quadratic vertex bound, rather than assume a cheap residual route. -/
theorem residual_route_quadratic (C : Finset (Fin d → ℝ))
    (A : Fin m → (Fin d → ℝ) →ₗ[ℝ] ℝ) (b : Fin m → ℝ)
    (hP : convexHull ℝ (C : Set (Fin d → ℝ))=body A b)
    (v : Fin d → ℝ) (hv : v ∈ (body A b).extremePoints ℝ)
    (B : Finset (Fin m)) (hB : B.card ≤ 3)
    (u : Fin d → ℝ) (hu : u ∈ residual C A b v B) :
    ∃ p : CoordinateRoute.Route (Edge A b v) (residual C A b v B) u v,
      p.length ≤ m*m := by
  classical
  let D := residual C A b v B
  obtain ⟨h,hh⟩ := HullCoordinate.strict_vertex_functional C v (hP.symm ▸ hv)
  let f : (Fin d → ℝ) →ₗ[ℝ] ℝ := -h
  have hstep : ∀ x ∈ D, x ≠ v → ∃ y ∈ D, Edge A b v x y ∧ f x < f y := by
    intro x hx hne
    have hxV := (Finset.mem_filter.mp hx).1
    have hxC : x ∈ C := (Finset.mem_filter.mp hxV).1
    have hxE : x ∈ (body A b).extremePoints ℝ := (Finset.mem_filter.mp hxV).2
    have hxG := (Finset.mem_filter.mp hx).2
    have hfx : f x < f v := by
      have ht := hh x hxC hne
      rw [map_sub] at ht
      change -h x < -h v
      linarith
    obtain ⟨y,hy,he,hinc⟩ := improve_locked C A b hP v hv x hxE f hfx
    have hyV : y ∈ vertexSet C A b :=
      Finset.mem_filter.mpr ⟨extremePoints_convexHull_subset (hP.symm ▸ hy),hy⟩
    have hyG : ∀ i ∈ good A b v B, A i y=b i := by
      intro i hi
      exact he.2.2 i ((mem_active A b v i).mp (Finset.mem_sdiff.mp hi).1) (hxG i hi)
    exact ⟨y,Finset.mem_filter.mpr ⟨hyV,hyG⟩,he,hinc⟩
  obtain ⟨p,hp⟩ := finite_ascent D (Edge A b v) f v hstep u hu
  have hc : D.card ≤ m*m+1 := residual_card_quadratic C A b v hv B hB
  exact ⟨p,by omega⟩

/-- Three exceptional original target rows have a quadratic original-row
route bound, improving the cubic specialization of the optional-slot count. -/
theorem three_exception_routes (C : Finset (Fin d → ℝ))
    (A : Fin m → (Fin d → ℝ) →ₗ[ℝ] ℝ) (b : Fin m → ℝ)
    (hP : convexHull ℝ (C : Set (Fin d → ℝ))=body A b)
    (v : Fin d → ℝ) (hv : v ∈ (body A b).extremePoints ℝ)
    (B : Finset (Fin m)) (hB : B.card ≤ 3)
    (htwo : ∀ i, i ∉ B → A i v=b i → ∃ lo : ℝ,
      ∀ x ∈ (body A b).extremePoints ℝ, A i x=lo ∨ A i x=b i)
    (u : Fin d → ℝ) (hu : u ∈ (body A b).extremePoints ℝ) :
    ∃ p : CoordinateRoute.Route (Edge A b v) (vertexSet C A b) u v,
      p.length ≤ (m-d)+m*m := by
  classical
  obtain ⟨w,hw,p,hp⟩ := enter_residual C A b hP v hv B htwo u hu
  obtain ⟨q,hq⟩ := residual_route_quadratic C A b hP v hv B hB w hw
  have hsub : residual C A b v B ⊆ vertexSet C A b := Finset.filter_subset _ _
  have ht : todo A b v B u ⊆ missing A b v u := by
    intro i hi
    obtain ⟨hiG,hiu⟩ := Finset.mem_filter.mp hi
    exact (mem_missing A b v u i).mpr
      ⟨(mem_active A b v i).mp (Finset.mem_sdiff.mp hiG).1,hiu⟩
  have hcost := (Finset.card_le_card ht).trans (missing_bound A b u v hu)
  refine ⟨p.append (q.mono hsub),?_⟩
  change p.length+q.length ≤ (m-d)+m*m
  omega

end Hirsch.SpatialResidual

/-- Original-edge routes with at most three unrestricted target rows.
The residual dimension, planar slice bounds, incidence count and walk are derived. -/
theorem solution (d m : ℕ) (C : Finset (Fin d → ℝ))
    (A : Fin m → (Fin d → ℝ) →ₗ[ℝ] ℝ) (b : Fin m → ℝ)
    (hP : convexHull ℝ (C : Set (Fin d → ℝ))={x | ∀ i, A i x ≤ b i})
    (B : Finset (Fin m)) (hB : B.card ≤ 3) (u v : Fin d → ℝ)
    (hu : u ∈ ({x | ∀ i, A i x ≤ b i} : Set (Fin d → ℝ)).extremePoints ℝ)
    (hv : v ∈ ({x | ∀ i, A i x ≤ b i} : Set (Fin d → ℝ)).extremePoints ℝ)
    (htwo : ∀ i, i ∉ B → A i v=b i → ∃ lo : ℝ,
      ∀ x ∈ ({x | ∀ j, A j x ≤ b j} : Set (Fin d → ℝ)).extremePoints ℝ,
        A i x=lo ∨ A i x=b i) :
    ∃ L : ℕ, L ≤ (m-d)+m*m ∧
      ∃ p : Fin (L+1) → (Fin d → ℝ), p 0=u ∧ p (Fin.last L)=v ∧
        (∀ t, p t ∈ ({x | ∀ i, A i x ≤ b i} : Set (Fin d → ℝ)).extremePoints ℝ) ∧
        ∀ t : Fin L, p t.castSucc ≠ p t.succ ∧
          IsExtreme ℝ {x : Fin d → ℝ | ∀ i, A i x ≤ b i}
            (segment ℝ (p t.castSucc) (p t.succ)) ∧
          (∀ i, A i v=b i → A i (p t.castSucc)=b i → A i (p t.succ)=b i) := by
  classical
  obtain ⟨p,hp⟩ := Hirsch.SpatialResidual.three_exception_routes C A b hP v hv B hB htwo u hu
  refine ⟨p.length,hp,fun t => p.point t.val,p.first,p.last,?_,?_⟩
  · intro t
    exact (Finset.mem_filter.mp (p.mem t.val (by have h := t.isLt; omega))).2
  · intro t
    exact p.step t.val t.isLt

#print axioms Hirsch.PlanarResidual.planar_vertex_card
#print axioms Hirsch.SpatialResidual.spatial_row_slice_card
#print axioms Hirsch.SpatialResidual.spatial_vertex_card
#print axioms Hirsch.SpatialResidual.residual_card_quadratic
#print axioms Hirsch.SpatialResidual.residual_route_quadratic
#print axioms Hirsch.SpatialResidual.three_exception_routes
#print axioms solution
