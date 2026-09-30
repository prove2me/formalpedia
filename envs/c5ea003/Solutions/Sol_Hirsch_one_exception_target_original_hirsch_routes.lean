-- Prove2me | solution 1 for Hirsch.one_exception_target_original_hirsch_routes
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-21T23:32:17.129666+00:00
-- url     : https://prove2.me/submissions/679b2373-2760-4a2f-89d5-21eb31e8ca78

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

/-- Ordinary original edge, preservation of every acquired target row, and
at least one newly acquired original target row. -/
def Step (A : Fin m → (Fin d → ℝ) →ₗ[ℝ] ℝ) (b : Fin m → ℝ)
    (v u w : Fin d → ℝ) : Prop :=
  u ≠ w ∧ IsExtreme ℝ (body A b) (segment ℝ u w) ∧
    (∀ i, A i v=b i → A i u=b i → A i w=b i) ∧
    ∃ i, A i v=b i ∧ A i u ≠ b i ∧ A i w=b i

/-- Only target-tight rows need two vertex values. A genuine improving edge
then acquires a target row in ONE original step; this is derived, not assumed. -/
theorem acquiring_step (C : Finset (Fin d → ℝ))
    (A : Fin m → (Fin d → ℝ) →ₗ[ℝ] ℝ) (b : Fin m → ℝ)
    (hP : convexHull ℝ (C : Set (Fin d → ℝ))=body A b)
    (v : Fin d → ℝ) (hv : v ∈ (body A b).extremePoints ℝ)
    (htwo : ∀ i, A i v=b i → ∃ lo : ℝ, ∀ x ∈ (body A b).extremePoints ℝ,
      A i x=lo ∨ A i x=b i)
    (u : Fin d → ℝ) (hu : u ∈ (body A b).extremePoints ℝ) (hne : u ≠ v) :
    ∃ w ∈ (body A b).extremePoints ℝ, Step A b v u w := by
  classical
  have huC : u ∈ C := extremePoints_convexHull_subset (hP.symm ▸ hu)
  have hvC : v ∈ C := extremePoints_convexHull_subset (hP.symm ▸ hv)
  have hexists : ∃ j, A j v=b j ∧ A j u < b j := by
    by_contra hn
    apply hne
    apply determined_by_active A b v hv u
    intro j hj
    by_contra hnot
    exact hn ⟨j,hj,lt_of_le_of_ne (hu.1 j) hnot⟩
  obtain ⟨j,hjv,hju⟩ := hexists
  let S := active A b u ∩ active A b v
  let D := locked C A b S
  have htarget : ∀ i ∈ S, A i v=b i := by
    intro i hi
    exact (mem_active A b v i).mp (Finset.mem_inter.mp hi).2
  have hsource : ∀ i ∈ S, A i u=b i := by
    intro i hi
    exact (mem_active A b u i).mp (Finset.mem_inter.mp hi).1
  have hface := locked_face C A b hP v hvC S htarget
  have huD : u ∈ D := Finset.mem_filter.mpr ⟨huC,hsource⟩
  have hvD : v ∈ D := Finset.mem_filter.mpr ⟨hvC,htarget⟩
  have huK : u ∈ convexHull ℝ (D : Set (Fin d → ℝ)) := subset_convexHull ℝ _ huD
  have hvK : v ∈ convexHull ℝ (D : Set (Fin d → ℝ)) := subset_convexHull ℝ _ hvD
  have huE : u ∈ (convexHull ℝ (D : Set (Fin d → ℝ))).extremePoints ℝ :=
    inter_extremePoints_subset_extremePoints_of_subset hface.subset ⟨huK,hu⟩
  have himp : A j u < A j v := by rw [hjv]; exact hju
  obtain ⟨w,hwD,hwE,hjw,huw,hseg⟩ := HullCoordinate.improving_edge D (A j) u v huE hvK himp
  have hw : w ∈ (body A b).extremePoints ℝ := hface.extremePoints_subset_extremePoints hwE
  have hlock : ∀ i, A i v=b i → A i u=b i → A i w=b i := by
    intro i hiv hiu
    have hi : i ∈ S := Finset.mem_inter.mpr
      ⟨(mem_active A b u i).mpr hiu,(mem_active A b v i).mpr hiv⟩
    exact (Finset.mem_filter.mp hwD).2 i hi
  obtain ⟨lo,hlo⟩ := htwo j hjv
  have hnew : A j w=b j := by
    rcases hlo u hu with huLo | huT
    · rcases hlo w hw with hwLo | hwT
      · rw [huLo,hwLo] at hjw
        exact False.elim ((lt_irrefl lo) hjw)
      · exact hwT
    · exact False.elim ((ne_of_lt hju) huT)
  exact ⟨w,hw,huw,hface.trans hseg.isExtreme,hlock,j,hjv,ne_of_lt hju,hnew⟩

lemma missing_decreases (A : Fin m → (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (b : Fin m → ℝ) (v u w : Fin d → ℝ) (h : Step A b v u w) :
    (missing A b v w).card < (missing A b v u).card := by
  classical
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨?_,?_⟩
  · intro i hi
    obtain ⟨hiv,hiw⟩ := (mem_missing A b v w i).mp hi
    exact (mem_missing A b v u i).mpr ⟨hiv,fun hiu => hiw (h.2.2.1 i hiv hiu)⟩
  · intro he
    obtain ⟨i,hiv,hiu,hiw⟩ := h.2.2.2
    have hi : i ∈ missing A b v w := by
      rw [he]
      exact (mem_missing A b v u i).mpr ⟨hiv,hiu⟩
    exact ((mem_missing A b v w i).mp hi).2 hiw

/-- The complete route is built by induction on initially missing original
rows. Every edge decreases this finite integer; no route is input. -/
theorem locked_route (C : Finset (Fin d → ℝ))
    (A : Fin m → (Fin d → ℝ) →ₗ[ℝ] ℝ) (b : Fin m → ℝ)
    (hP : convexHull ℝ (C : Set (Fin d → ℝ))=body A b)
    (v : Fin d → ℝ) (hv : v ∈ (body A b).extremePoints ℝ)
    (htwo : ∀ i, A i v=b i → ∃ lo : ℝ, ∀ x ∈ (body A b).extremePoints ℝ,
      A i x=lo ∨ A i x=b i)
    (u : Fin d → ℝ) (hu : u ∈ (body A b).extremePoints ℝ) :
    ∃ p : CoordinateRoute.Route (Step A b v)
      (vertexSet C A b) u v,
      p.length ≤ (missing A b v u).card := by
  classical
  have hmem : ∀ x ∈ (body A b).extremePoints ℝ,
      x ∈ C.filter (fun y => y ∈ (body A b).extremePoints ℝ) := by
    intro x hx
    exact Finset.mem_filter.mpr ⟨extremePoints_convexHull_subset (hP.symm ▸ hx),hx⟩
  have aux : ∀ k : ℕ, ∀ x : Fin d → ℝ, x ∈ (body A b).extremePoints ℝ →
      (missing A b v x).card=k →
      ∃ p : CoordinateRoute.Route (Step A b v)
        (vertexSet C A b) x v,
        p.length ≤ (missing A b v x).card := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro x hx hk
      by_cases he : x=v
      · subst x
        exact ⟨CoordinateRoute.Route.nil (hmem v hv),by simp [CoordinateRoute.Route.nil]⟩
      obtain ⟨w,hw,hs⟩ := acquiring_step C A b hP v hv htwo x hx he
      have hdec := missing_decreases A b v x w hs
      obtain ⟨p,hp⟩ := ih (missing A b v w).card (by omega) w hw rfl
      refine ⟨CoordinateRoute.Route.prepend (hmem x hx) hs p,?_⟩
      change p.length+1 ≤ (missing A b v x).card
      omega
  exact aux (missing A b v u).card u hu rfl

end Hirsch.TargetRows

namespace Hirsch.OneException

open Set TargetRows

variable {d m : ℕ}

/-- Improve a chosen missing target row inside the whole retained original
face. There is no level assumption in this geometric construction. -/
lemma improve_locked_row (C : Finset (Fin d → ℝ))
    (A : Fin m → (Fin d → ℝ) →ₗ[ℝ] ℝ) (b : Fin m → ℝ)
    (hP : convexHull ℝ (C : Set (Fin d → ℝ))=body A b)
    (v : Fin d → ℝ) (hv : v ∈ (body A b).extremePoints ℝ)
    (u : Fin d → ℝ) (hu : u ∈ (body A b).extremePoints ℝ)
    (j : Fin m) (hjv : A j v=b j) (hju : A j u < b j) :
    ∃ w ∈ (body A b).extremePoints ℝ,
      u ≠ w ∧ IsExtreme ℝ (body A b) (segment ℝ u w) ∧
      (∀ i, A i v=b i → A i u=b i → A i w=b i) ∧ A j u < A j w := by
  classical
  have huC : u ∈ C := extremePoints_convexHull_subset (hP.symm ▸ hu)
  have hvC : v ∈ C := extremePoints_convexHull_subset (hP.symm ▸ hv)
  let S := active A b u ∩ active A b v
  let D := locked C A b S
  have htarget : ∀ i ∈ S, A i v=b i := by
    intro i hi
    exact (mem_active A b v i).mp (Finset.mem_inter.mp hi).2
  have hsource : ∀ i ∈ S, A i u=b i := by
    intro i hi
    exact (mem_active A b u i).mp (Finset.mem_inter.mp hi).1
  have hface := locked_face C A b hP v hvC S htarget
  have huD : u ∈ D := Finset.mem_filter.mpr ⟨huC,hsource⟩
  have hvD : v ∈ D := Finset.mem_filter.mpr ⟨hvC,htarget⟩
  have huK : u ∈ convexHull ℝ (D : Set (Fin d → ℝ)) := subset_convexHull ℝ _ huD
  have hvK : v ∈ convexHull ℝ (D : Set (Fin d → ℝ)) := subset_convexHull ℝ _ hvD
  have huE : u ∈ (convexHull ℝ (D : Set (Fin d → ℝ))).extremePoints ℝ :=
    inter_extremePoints_subset_extremePoints_of_subset hface.subset ⟨huK,hu⟩
  have himp : A j u < A j v := by rw [hjv]; exact hju
  obtain ⟨w,hwD,hwE,hjw,huw,hseg⟩ := HullCoordinate.improving_edge D (A j) u v huE hvK himp
  have hw : w ∈ (body A b).extremePoints ℝ := hface.extremePoints_subset_extremePoints hwE
  refine ⟨w,hw,huw,hface.trans hseg.isExtreme,?_,hjw⟩
  intro i hiv hiu
  have hi : i ∈ S := Finset.mem_inter.mpr
    ⟨(mem_active A b u i).mpr hiu,(mem_active A b v i).mpr hiv⟩
  exact (Finset.mem_filter.mp hwD).2 i hi

/-- When only one target row is still free, no actual improving vertex can
have an intermediate value. Active-kernel triviality derives the line; no
supplied dimension, adjacency, two-level or short-path premise is used. -/
lemma last_row_attained
    (A : Fin m → (Fin d → ℝ) →ₗ[ℝ] ℝ) (b : Fin m → ℝ)
    (u v w : Fin d → ℝ)
    (hu : u ∈ (body A b).extremePoints ℝ)
    (hv : v ∈ (body A b).extremePoints ℝ)
    (hw : w ∈ (body A b).extremePoints ℝ)
    (q : Fin m) (hqv : A q v=b q) (hqu : A q u < b q)
    (hlocked : ∀ i, A i v=b i → i ≠ q → A i u=b i ∧ A i w=b i)
    (hinc : A q u < A q w) : A q w=b q := by
  by_contra hn
  have hqw : A q w < b q := lt_of_le_of_ne (hw.1 q) hn
  have hden : 0 < b q-A q u := sub_pos.mpr hqu
  let t : ℝ := (A q w-A q u)/(b q-A q u)
  have ht0 : 0 < t := div_pos (sub_pos.mpr hinc) hden
  have ht1 : t < 1 := (div_lt_one hden).mpr (by linarith)
  have hprod : t*(b q-A q u)=A q w-A q u :=
    div_mul_cancel₀ _ (ne_of_gt hden)
  have heq : w=(1-t) • u+t • v := by
    apply sub_eq_zero.mp
    apply extreme_kernel A b v hv (w-((1-t) • u+t • v))
    intro i hi
    by_cases he : i=q
    · subst i
      simp only [map_sub,map_add,map_smul,smul_eq_mul,hqv]
      nlinarith [hprod]
    · obtain ⟨hiu,hiw⟩ := hlocked i hi he
      simp only [map_sub,map_add,map_smul,smul_eq_mul,hiu,hiw,hi]
      ring
  have hseg : w ∈ openSegment ℝ u v :=
    ⟨1-t,t,sub_pos.mpr ht1,ht0,by ring,heq.symm⟩
  have huw : u=w := hw.2 hu.1 hv.1 hseg
  rw [huw] at hinc
  exact (lt_irrefl _) hinc

/-- At most one exceptional target label, with completely unrestricted
vertex values, is compatible with acquiring a target label at every step. -/
theorem acquiring_step_one_exception (C : Finset (Fin d → ℝ))
    (A : Fin m → (Fin d → ℝ) →ₗ[ℝ] ℝ) (b : Fin m → ℝ)
    (hP : convexHull ℝ (C : Set (Fin d → ℝ))=body A b)
    (B : Finset (Fin m)) (hB : B.card ≤ 1)
    (v : Fin d → ℝ) (hv : v ∈ (body A b).extremePoints ℝ)
    (htwo : ∀ i, i ∉ B → A i v=b i → ∃ lo : ℝ,
      ∀ x ∈ (body A b).extremePoints ℝ, A i x=lo ∨ A i x=b i)
    (u : Fin d → ℝ) (hu : u ∈ (body A b).extremePoints ℝ) (hne : u ≠ v) :
    ∃ w ∈ (body A b).extremePoints ℝ, Step A b v u w := by
  classical
  by_cases hg : ∃ j, j ∉ B ∧ A j v=b j ∧ A j u < b j
  · obtain ⟨j,hjB,hjv,hju⟩ := hg
    obtain ⟨w,hw,huw,hedge,hlock,hinc⟩ := improve_locked_row C A b hP v hv u hu j hjv hju
    obtain ⟨lo,hlo⟩ := htwo j hjB hjv
    have hnew : A j w=b j := by
      rcases hlo u hu with huLo | huT
      · rcases hlo w hw with hwLo | hwT
        · rw [huLo,hwLo] at hinc
          exact False.elim ((lt_irrefl lo) hinc)
        · exact hwT
      · exact False.elim ((ne_of_lt hju) huT)
    exact ⟨w,hw,huw,hedge,hlock,j,hjv,ne_of_lt hju,hnew⟩
  · have hexists : ∃ q, A q v=b q ∧ A q u < b q := by
      by_contra hn
      apply hne
      apply determined_by_active A b v hv u
      intro i hi
      by_contra hnot
      exact hn ⟨i,hi,lt_of_le_of_ne (hu.1 i) hnot⟩
    obtain ⟨q,hqv,hqu⟩ := hexists
    have hqB : q ∈ B := by
      by_contra hnot
      exact hg ⟨q,hnot,hqv,hqu⟩
    have hother : ∀ i, A i v=b i → i ≠ q → A i u=b i := by
      intro i hiv hiq
      by_contra hnot
      have hiB : i ∈ B := by
        by_contra hiNB
        exact hg ⟨i,hiNB,hiv,lt_of_le_of_ne (hu.1 i) hnot⟩
      have hsub : ({i,q} : Finset (Fin m)) ⊆ B := by
        intro a ha
        rcases Finset.mem_insert.mp ha with ha | ha
        · subst a
          exact hiB
        · have haq : a=q := Finset.mem_singleton.mp ha
          subst a
          exact hqB
      have hc := Finset.card_le_card hsub
      rw [Finset.card_pair hiq] at hc
      omega
    obtain ⟨w,hw,huw,hedge,hlock,hinc⟩ := improve_locked_row C A b hP v hv u hu q hqv hqu
    have hnew : A q w=b q := last_row_attained A b u v w hu hv hw q hqv hqu
      (fun i hi hiq => ⟨hother i hi hiq,hlock i hi (hother i hi hiq)⟩) hinc
    exact ⟨w,hw,huw,hedge,hlock,q,hqv,ne_of_lt hqu,hnew⟩

/-- Induction charges original edges to genuinely new original target labels.
The exceptional row does not contribute its number of levels to the bound. -/
theorem locked_route_one_exception (C : Finset (Fin d → ℝ))
    (A : Fin m → (Fin d → ℝ) →ₗ[ℝ] ℝ) (b : Fin m → ℝ)
    (hP : convexHull ℝ (C : Set (Fin d → ℝ))=body A b)
    (B : Finset (Fin m)) (hB : B.card ≤ 1)
    (v : Fin d → ℝ) (hv : v ∈ (body A b).extremePoints ℝ)
    (htwo : ∀ i, i ∉ B → A i v=b i → ∃ lo : ℝ,
      ∀ x ∈ (body A b).extremePoints ℝ, A i x=lo ∨ A i x=b i)
    (u : Fin d → ℝ) (hu : u ∈ (body A b).extremePoints ℝ) :
    ∃ p : CoordinateRoute.Route (Step A b v) (vertexSet C A b) u v,
      p.length ≤ (missing A b v u).card := by
  classical
  have hmem : ∀ x ∈ (body A b).extremePoints ℝ,
      x ∈ C.filter (fun y => y ∈ (body A b).extremePoints ℝ) := by
    intro x hx
    exact Finset.mem_filter.mpr ⟨extremePoints_convexHull_subset (hP.symm ▸ hx),hx⟩
  have aux : ∀ k : ℕ, ∀ x : Fin d → ℝ, x ∈ (body A b).extremePoints ℝ →
      (missing A b v x).card=k →
      ∃ p : CoordinateRoute.Route (Step A b v) (vertexSet C A b) x v,
        p.length ≤ (missing A b v x).card := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro x hx hk
      by_cases he : x=v
      · subst x
        exact ⟨CoordinateRoute.Route.nil (hmem v hv),by simp [CoordinateRoute.Route.nil]⟩
      obtain ⟨w,hw,hs⟩ := acquiring_step_one_exception C A b hP B hB v hv htwo x hx he
      have hdec := missing_decreases A b v x w hs
      obtain ⟨p,hp⟩ := ih (missing A b v w).card (by omega) w hw rfl
      refine ⟨CoordinateRoute.Route.prepend (hmem x hx) hs p,?_⟩
      change p.length+1 ≤ (missing A b v x).card
      omega
  exact aux (missing A b v u).card u hu rfl

end Hirsch.OneException

/-- One exceptional target row may have arbitrarily many vertex values. -/
theorem solution (d m : ℕ) (C : Finset (Fin d → ℝ))
    (A : Fin m → (Fin d → ℝ) →ₗ[ℝ] ℝ) (b : Fin m → ℝ)
    (hP : convexHull ℝ (C : Set (Fin d → ℝ))={x | ∀ i, A i x ≤ b i})
    (B : Finset (Fin m)) (hB : B.card ≤ 1)
    (u v : Fin d → ℝ)
    (hu : u ∈ ({x | ∀ i, A i x ≤ b i} : Set (Fin d → ℝ)).extremePoints ℝ)
    (hv : v ∈ ({x | ∀ i, A i x ≤ b i} : Set (Fin d → ℝ)).extremePoints ℝ)
    (htwo : ∀ i, i ∉ B → A i v=b i → ∃ lo : ℝ,
      ∀ x ∈ ({x | ∀ j, A j x ≤ b j} : Set (Fin d → ℝ)).extremePoints ℝ,
        A i x=lo ∨ A i x=b i) :
    ∃ L : ℕ, L ≤ m-d ∧
      L ≤ (@Finset.filter (Fin m) (fun i => A i v=b i ∧ A i u ≠ b i)
        (fun _ => Classical.propDecidable _) Finset.univ).card ∧
      ∃ p : Fin (L+1) → (Fin d → ℝ), p 0=u ∧ p (Fin.last L)=v ∧
        (∀ t, p t ∈ ({x | ∀ i, A i x ≤ b i} : Set (Fin d → ℝ)).extremePoints ℝ) ∧
        ∀ t : Fin L, p t.castSucc ≠ p t.succ ∧
          IsExtreme ℝ {x : Fin d → ℝ | ∀ i, A i x ≤ b i}
            (segment ℝ (p t.castSucc) (p t.succ)) ∧
          (∀ i, A i v=b i → A i (p t.castSucc)=b i → A i (p t.succ)=b i) ∧
          ∃ i, A i v=b i ∧ A i (p t.castSucc) ≠ b i ∧ A i (p t.succ)=b i := by
  classical
  obtain ⟨p,hp⟩ := Hirsch.OneException.locked_route_one_exception C A b hP B hB v hv htwo u hu
  have hset : Hirsch.TargetRows.missing A b v u =
      @Finset.filter (Fin m) (fun i => A i v=b i ∧ A i u ≠ b i)
        (fun _ => Classical.propDecidable _) Finset.univ := by
    ext i
    simp only [Hirsch.TargetRows.mem_missing,Finset.mem_filter,Finset.mem_univ,true_and]
  refine ⟨p.length,hp.trans (Hirsch.TargetRows.missing_bound A b u v hu),?_,
    fun t => p.point t.val,p.first,p.last,?_,?_⟩
  · rw [← hset]
    exact hp
  · intro t
    exact (Finset.mem_filter.mp (p.mem t.val (by have h := t.isLt; omega))).2
  · intro t
    exact p.step t.val t.isLt

#print axioms Hirsch.OneException.improve_locked_row
#print axioms Hirsch.OneException.last_row_attained
#print axioms Hirsch.OneException.acquiring_step_one_exception
#print axioms Hirsch.OneException.locked_route_one_exception
#print axioms solution
