-- Prove2me | solution 1 for Hirsch.original_row_radial_max_envelope
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-24T03:39:34.716372+00:00
-- url     : https://prove2.me/submissions/ccc4850c-ffa8-4e0a-8cec-dd856d7c530c

import Mathlib

open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

-- Unchanged accepted helper bodies from PR340 (see dependency-identities.json).
namespace Hirsch.HullCoordinate
open Set
variable {d : ℕ}

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


end Hirsch.HullCoordinate

namespace Hirsch.TargetRows
open Set
variable {d m : ℕ}

def body (A : Fin m → (Fin d → ℝ) →ₗ[ℝ] ℝ) (b : Fin m → ℝ) : Set (Fin d → ℝ) :=
  {x | ∀ i, A i x ≤ b i}

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


end Hirsch.TargetRows

namespace Hirsch.RadialRowEnvelope

open Set TargetRows
variable {d m : ℕ}

lemma scaled_eval (f : (Fin d → ℝ) →ₗ[ℝ] ℝ) (v y : Fin d → ℝ) (a : ℝ) :
    f (v + (1 / a) • y) = f v + f y / a := by
  simp only [map_add, map_smul, smul_eq_mul, one_div, div_eq_mul_inv]
  ring

lemma scaled_row (f : (Fin d → ℝ) →ₗ[ℝ] ℝ) (b : ℝ)
    (v y : Fin d → ℝ) (a : ℝ) (ha : 0 < a) :
    f (v + (1 / a) • y) ≤ b ↔ f y ≤ a * (b - f v) := by
  rw [scaled_eval]
  constructor
  · intro hx
    have he : f y / a ≤ b - f v := by linarith
    have hh := (div_le_iff₀ ha).mp he
    nlinarith
  · intro hy
    have he : f y / a ≤ b - f v :=
      (div_le_iff₀ ha).mpr (by nlinarith)
    linarith

lemma scaled_tight (f : (Fin d → ℝ) →ₗ[ℝ] ℝ) (b : ℝ)
    (v y : Fin d → ℝ) (a : ℝ) (ha : 0 < a) :
    f (v + (1 / a) • y) = b ↔ f y = a * (b - f v) := by
  rw [scaled_eval]
  constructor
  · intro hx
    have he : f y / a = b - f v := by linarith
    have hh := congrArg (fun z : ℝ => z * a) he
    change (f y / a) * a = (b - f v) * a at hh
    rw [div_mul_cancel₀ _ (ne_of_gt ha)] at hh
    nlinarith
  · intro hy
    have he : f y / a = b - f v := by
      apply mul_right_cancel₀ (ne_of_gt ha)
      rw [div_mul_cancel₀ _ (ne_of_gt ha)]
      nlinarith
    linarith

/-- Exact transformation of every original row, with target-tight rows kept
as directional constraints rather than divided by zero. -/
theorem epigraph_iff (A : Fin m → (Fin d → ℝ) →ₗ[ℝ] ℝ) (b : Fin m → ℝ)
    (v : Fin d → ℝ) (hv : v ∈ body A b) (y : Fin d → ℝ)
    (a : ℝ) (ha : 0 < a) :
    v + (1 / a) • y ∈ body A b ↔
      (∀ i, A i v = b i → A i y ≤ 0) ∧
      (∀ i, A i v < b i → A i y / (b i - A i v) ≤ a) := by
  constructor
  · intro hx
    constructor
    · intro i hi
      have hh := (scaled_row (A i) (b i) v y a ha).mp (hx i)
      simpa only [hi, sub_self, mul_zero] using hh
    · intro i hi
      exact (div_le_iff₀ (sub_pos.mpr hi)).mpr
        ((scaled_row (A i) (b i) v y a ha).mp (hx i))
  · rintro ⟨htarget, hother⟩ i
    apply (scaled_row (A i) (b i) v y a ha).mpr
    by_cases hi : A i v = b i
    · simpa only [hi, sub_self, mul_zero] using htarget i hi
    · have hp : A i v < b i := lt_of_le_of_ne (hv i) hi
      exact (div_le_iff₀ (sub_pos.mpr hp)).mp (hother i hp)

/-- Strict exposure extends from the finite generators to the whole body. -/
lemma strict_on_body (C : Finset (Fin d → ℝ))
    (A : Fin m → (Fin d → ℝ) →ₗ[ℝ] ℝ) (b : Fin m → ℝ)
    (hP : convexHull ℝ (C : Set (Fin d → ℝ)) = body A b)
    (v : Fin d → ℝ) (h : (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (hh : ∀ z ∈ C, z ≠ v → 0 < h (z - v)) :
    ∀ x ∈ body A b, x ≠ v → 0 < h (x - v) := by
  have hC : ∀ z ∈ C, (-h) z ≤ (-h) v ∧
      ((-h) z = (-h) v → z ∈ ({v} : Set (Fin d → ℝ))) := by
    intro z hz
    change -h z ≤ -h v ∧ (-h z = -h v → z ∈ ({v} : Set (Fin d → ℝ)))
    by_cases he : z = v
    · subst z
      exact ⟨le_rfl, fun _ => Set.mem_singleton v⟩
    · have hp := hh z hz he
      rw [map_sub] at hp
      exact ⟨by linarith, fun heq => False.elim (by linarith)⟩
  have hs := HullCoordinate.hull_support C (-h) ((-h) v) {v}
    (convex_singleton v) hC
  intro x hx hxv
  obtain ⟨hle, heq⟩ := hs x (by rw [hP]; exact hx)
  have hle' : h v ≤ h x := by
    change -h x ≤ -h v at hle
    linarith
  have hne : h x ≠ h v := by
    intro he
    have he' : (-h) x = (-h) v := by change -h x = -h v; rw [he]
    exact hxv (Set.mem_singleton_iff.mp (heq he'))
  rw [map_sub]
  exact sub_pos.mpr (lt_of_le_of_ne hle' (Ne.symm hne))

lemma height_bound (C : Finset (Fin d → ℝ))
    (A : Fin m → (Fin d → ℝ) →ₗ[ℝ] ℝ) (b : Fin m → ℝ)
    (hP : convexHull ℝ (C : Set (Fin d → ℝ)) = body A b)
    (v : Fin d → ℝ) (hvC : v ∈ C) (h : (Fin d → ℝ) →ₗ[ℝ] ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ body A b, h (x - v) ≤ B := by
  classical
  obtain ⟨w, hw, hmax⟩ := Finset.exists_max_image C h ⟨v, hvC⟩
  have hs := HullCoordinate.hull_support C h (h w) Set.univ convex_univ
    (fun z hz => ⟨hmax z hz, fun _ => Set.mem_univ z⟩)
  refine ⟨h w - h v, sub_nonneg.mpr (hmax v hvC), ?_⟩
  intro x hx
  have hb := (hs x (by rw [hP]; exact hx)).1
  rw [map_sub]
  linarith

/-- Every normalized feasible target-cone direction meets an original row
not containing the target. No artificial cap or extra row is introduced. -/
lemma positive_piece (C : Finset (Fin d → ℝ))
    (A : Fin m → (Fin d → ℝ) →ₗ[ℝ] ℝ) (b : Fin m → ℝ)
    (hP : convexHull ℝ (C : Set (Fin d → ℝ)) = body A b)
    (v : Fin d → ℝ) (hvC : v ∈ C) (hv : v ∈ body A b)
    (h : (Fin d → ℝ) →ₗ[ℝ] ℝ) (y : Fin d → ℝ)
    (hy : h y = 1) (ht : ∀ i, A i v = b i → A i y ≤ 0) :
    ∃ i : Fin m, A i v < b i ∧ 0 < A i y := by
  classical
  by_contra hn
  have hrows : ∀ i, A i y ≤ 0 := by
    intro i
    by_cases hi : A i v = b i
    · exact ht i hi
    · have hp : A i v < b i := lt_of_le_of_ne (hv i) hi
      exact le_of_not_gt (fun hz => hn ⟨i, hp, hz⟩)
  obtain ⟨B, hB, hbound⟩ := height_bound C A b hP v hvC h
  have hp : v + (B + 1) • y ∈ body A b := by
    intro i
    simp only [map_add, map_smul, smul_eq_mul]
    have hz := mul_nonpos_of_nonneg_of_nonpos
      (show 0 ≤ B + 1 by linarith) (hrows i)
    linarith [hv i]
  have hh := hbound (v + (B + 1) • y) hp
  have he : h (v + (B + 1) • y - v) = B + 1 := by
    simp only [map_sub, map_add, map_smul, smul_eq_mul, hy]
    ring
  rw [he] at hh
  linarith

/-- The lower boundary of the transformed body is the attained positive
maximum of at most m original-row affine functions, in every dimension. -/
theorem ray_threshold (C : Finset (Fin d → ℝ))
    (A : Fin m → (Fin d → ℝ) →ₗ[ℝ] ℝ) (b : Fin m → ℝ)
    (hP : convexHull ℝ (C : Set (Fin d → ℝ)) = body A b)
    (v : Fin d → ℝ) (hvC : v ∈ C) (hv : v ∈ body A b)
    (h : (Fin d → ℝ) →ₗ[ℝ] ℝ) (y : Fin d → ℝ)
    (hy : h y = 1) (ht : ∀ i, A i v = b i → A i y ≤ 0) :
    ∃ i : Fin m, A i v < b i ∧ 0 < A i y / (b i - A i v) ∧
      (∀ j, A j v < b j → A j y / (b j - A j v) ≤ A i y / (b i - A i v)) ∧
      ∀ a : ℝ, 0 < a →
        (v + (1 / a) • y ∈ body A b ↔ A i y / (b i - A i v) ≤ a) := by
  classical
  let I := Finset.univ.filter (fun i : Fin m => A i v < b i)
  let f := fun i : Fin m => A i y / (b i - A i v)
  obtain ⟨j, hj, hjy⟩ := positive_piece C A b hP v hvC hv h y hy ht
  have hjI : j ∈ I := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩
  obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image I f ⟨j, hjI⟩
  have hi' : A i v < b i := (Finset.mem_filter.mp hi).2
  have hjpos : 0 < f j := div_pos hjy (sub_pos.mpr hj)
  have hupper : ∀ k, A k v < b k → f k ≤ f i := by
    intro k hk
    exact hmax k (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩)
  refine ⟨i, hi', lt_of_lt_of_le hjpos (hmax j hjI), hupper, ?_⟩
  intro a ha
  constructor
  · intro hx
    exact ((epigraph_iff A b v hv y a ha).mp hx).2 i hi'
  · intro hia
    exact (epigraph_iff A b v hv y a ha).mpr
      ⟨ht, fun k hk => (hupper k hk).trans hia⟩

/-- A non-target original vertex must be tight on a row not tight at v. -/
lemma non_target_active (A : Fin m → (Fin d → ℝ) →ₗ[ℝ] ℝ) (b : Fin m → ℝ)
    (v x : Fin d → ℝ) (hv : v ∈ body A b)
    (hx : x ∈ (body A b).extremePoints ℝ) (hxv : x ≠ v) :
    ∃ i : Fin m, A i x = b i ∧ A i v < b i := by
  classical
  by_contra hn
  have hz := TargetRows.extreme_kernel A b x hx (v - x) (by
    intro i hi
    have he : A i v = b i := by
      by_contra he
      exact hn ⟨i, hi, lt_of_le_of_ne (hv i) he⟩
    rw [map_sub, he, hi, sub_self])
  exact hxv (sub_eq_zero.mp hz).symm

lemma chart_reconstruct (h : (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (v x : Fin d → ℝ) (hx : 0 < h (x - v)) :
    v + (1 / (1 / h (x - v))) • ((1 / h (x - v)) • (x - v)) = x := by
  have hc : h (x - v) * (1 / h (x - v)) = 1 := by
    rw [mul_comm]
    exact div_mul_cancel₀ _ (ne_of_gt hx)
  simp only [one_div, inv_inv, smul_smul] at *
  rw [hc, one_smul]
  abel

/-- Every original non-target vertex lies on the max-envelope, with all
original tight-row labels retained, including target-tight and zero rows. -/
theorem vertex_envelope (A : Fin m → (Fin d → ℝ) →ₗ[ℝ] ℝ) (b : Fin m → ℝ)
    (v x : Fin d → ℝ) (hv : v ∈ body A b)
    (hx : x ∈ (body A b).extremePoints ℝ) (hxv : x ≠ v)
    (h : (Fin d → ℝ) →ₗ[ℝ] ℝ) (hhx : 0 < h (x - v)) :
    let y := (1 / h (x - v)) • (x - v)
    let a := 1 / h (x - v)
    h y = 1 ∧ v + (1 / a) • y = x ∧
      (∀ i, A i x = b i ↔ A i y = a * (b i - A i v)) ∧
      (∀ i, A i v < b i → A i y / (b i - A i v) ≤ a) ∧
      ∃ i, A i v < b i ∧ A i y / (b i - A i v) = a := by
  let y := (1 / h (x - v)) • (x - v)
  let a := 1 / h (x - v)
  have ha : 0 < a := div_pos (by norm_num) hhx
  have hr : v + (1 / a) • y = x := chart_reconstruct h v x hhx
  have hy : h y = 1 := by
    change h ((1 / h (x - v)) • (x - v)) = 1
    rw [map_smul]
    change (1 / h (x - v)) * h (x - v) = 1
    exact div_mul_cancel₀ _ (ne_of_gt hhx)
  have ht : ∀ i, A i x = b i ↔ A i y = a * (b i - A i v) := by
    intro i
    have he := scaled_tight (A i) (b i) v y a ha
    rwa [hr] at he
  have hu := ((epigraph_iff A b v hv y a ha).mp (by rw [hr]; exact hx.1)).2
  obtain ⟨i, hi, hiv⟩ := non_target_active A b v x hv hx hxv
  refine ⟨hy, hr, ht, hu, i, hiv, ?_⟩
  apply mul_right_cancel₀ (ne_of_gt (sub_pos.mpr hiv))
  rw [div_mul_cancel₀ _ (ne_of_gt (sub_pos.mpr hiv))]
  exact (ht i).mp hi

/-- No original non-target vertices are merged by radial normalization. -/
theorem vertex_injective (A : Fin m → (Fin d → ℝ) →ₗ[ℝ] ℝ) (b : Fin m → ℝ)
    (v : Fin d → ℝ) (hv : v ∈ body A b) (h : (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (hh : ∀ x ∈ body A b, x ≠ v → 0 < h (x - v)) :
    Set.InjOn (fun x => (1 / h (x - v)) • (x - v))
      ((body A b).extremePoints ℝ \ {v}) := by
  intro x hx z hz he
  change (1 / h (x - v)) • (x - v) = (1 / h (z - v)) • (z - v) at he
  have hxv : x ≠ v := by simpa only [Set.mem_singleton_iff] using hx.2
  have hzv : z ≠ v := by simpa only [Set.mem_singleton_iff] using hz.2
  obtain ⟨_, hxr, _, hxu, i, hi, hxi⟩ := vertex_envelope A b v x hv hx.1 hxv h
    (hh x hx.1.1 hxv)
  obtain ⟨_, hzr, _, hzu, j, hj, hzj⟩ := vertex_envelope A b v z hv hz.1 hzv h
    (hh z hz.1.1 hzv)
  have hxle : 1 / h (x - v) ≤ 1 / h (z - v) := by
    rw [← hxi, he]
    exact hzu i hi
  have hzle : 1 / h (z - v) ≤ 1 / h (x - v) := by
    rw [← hzj, ← he]
    exact hxu j hj
  have ha := le_antisymm hxle hzle
  calc
    x = v + (1 / (1 / h (x - v))) • ((1 / h (x - v)) • (x - v)) := hxr.symm
    _ = v + (1 / (1 / h (z - v))) • ((1 / h (z - v)) • (z - v)) := by rw [he, ha]
    _ = z := hzr

/-- A direction annihilating all active original rows is locally feasible.
The step size is derived from finite original slacks, not supplied. -/
lemma forward_tangent_feasible (A : Fin m → (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (b : Fin m → ℝ) (x z : Fin d → ℝ) (hx : x ∈ body A b)
    (hz : ∀ i, A i x = b i → A i z = 0) :
    ∃ e : ℝ, 0 < e ∧ x + e • z ∈ body A b := by
  classical
  let S := Finset.univ.filter (fun i : Fin m => A i x ≠ b i)
  have hs : ∀ i ∈ S, 0 < b i - A i x := by
    intro i hi
    exact sub_pos.mpr (lt_of_le_of_ne (hx i) (Finset.mem_filter.mp hi).2)
  obtain ⟨e, he, hsmall⟩ := HullCoordinate.finite_margin S
    (fun i => b i - A i x) (fun i => A i z) hs
  refine ⟨e, he, ?_⟩
  intro i
  by_cases hi : A i x = b i
  · simp only [map_add, map_smul, smul_eq_mul, hz i hi, mul_zero, add_zero]
    exact hx i
  · have hb := hsmall i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
    have hab := mul_le_mul_of_nonneg_left (le_abs_self (A i z)) he.le
    simp only [map_add, map_smul, smul_eq_mul]
    linarith

/-- Every original exposed segment avoiding v has a supporting ORIGINAL row
that is slack at v and tight at both endpoints. This is a row-charge witness,
not a bound on how many times that row can be used. -/
theorem exposed_edge_row (A : Fin m → (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (b : Fin m → ℝ) (v u w : Fin d → ℝ) (hv : v ∈ body A b)
    (hu : u ∈ body A b) (hw : w ∈ body A b)
    (hE : IsExposed ℝ (body A b) (segment ℝ u w))
    (hvout : v ∉ segment ℝ u w) :
    ∃ i : Fin m, A i v < b i ∧ A i u = b i ∧ A i w = b i := by
  classical
  obtain ⟨f, hf⟩ := hE ⟨u, left_mem_segment ℝ u w⟩
  let x := (1 / 2 : ℝ) • u + (1 / 2 : ℝ) • w
  have hxseg : x ∈ segment ℝ u w :=
    ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, rfl⟩
  have hxF : x ∈ body A b ∧ ∀ z ∈ body A b, f z ≤ f x := by
    change x ∈ {z ∈ body A b | ∀ y ∈ body A b, f y ≤ f z}
    rw [← hf]
    exact hxseg
  have hgap : f v < f x := by
    apply lt_of_le_of_ne (hxF.2 v hv)
    intro he
    apply hvout
    rw [hf]
    exact ⟨hv, fun z hz => by rw [he]; exact hxF.2 z hz⟩
  by_contra hn
  have hactive : ∀ i, A i x = b i → A i v = b i := by
    intro i hi
    have hm : A i x = (A i u + A i w) / 2 := by
      dsimp [x]
      simp only [map_add, map_smul, smul_eq_mul]
      ring
    have hu' : A i u = b i := by linarith [hu i, hw i]
    have hw' : A i w = b i := by linarith [hu i, hw i]
    by_contra hi'
    exact hn ⟨i, lt_of_le_of_ne (hv i) hi', hu', hw'⟩
  obtain ⟨e, he, hs⟩ := forward_tangent_feasible A b x (x - v) hxF.1 (by
    intro i hi
    rw [map_sub, hi, hactive i hi, sub_self])
  have hmax := hxF.2 (x + e • (x - v)) hs
  simp only [map_add, map_smul, map_sub, smul_eq_mul] at hmax
  have hp := mul_pos he (sub_pos.mpr hgap)
  linarith

lemma extreme_not_in_other_segment (A : Fin m → (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (b : Fin m → ℝ) (v u w : Fin d → ℝ)
    (hv : v ∈ (body A b).extremePoints ℝ)
    (hu : u ∈ body A b) (hw : w ∈ body A b)
    (huv : u ≠ v) (hwv : w ≠ v) : v ∉ segment ℝ u w := by
  intro hs
  obtain ⟨a, c, ha, hc, hac, he⟩ := hs
  by_cases ha0 : a = 0
  · have hc1 : c = 1 := by linarith
    exact hwv (by simpa only [ha0, hc1, zero_smul, one_smul, zero_add] using he)
  by_cases hc0 : c = 0
  · have ha1 : a = 1 := by linarith
    exact huv (by simpa only [hc0, ha1, zero_smul, one_smul, add_zero] using he)
  have ho : v ∈ openSegment ℝ u w :=
    ⟨a, c, lt_of_le_of_ne ha (Ne.symm ha0), lt_of_le_of_ne hc (Ne.symm hc0), hac, he⟩
  exact huv (hv.2 hu hw ho)


end Hirsch.RadialRowEnvelope

/-- An arbitrary-dimensional original finite-H polytope has an exact radial
max-envelope using only its original rows, with no lost non-target vertices. -/
theorem solution (d m : ℕ) (C : Finset (Fin d → ℝ))
    (A : Fin m → (Fin d → ℝ) →ₗ[ℝ] ℝ) (b : Fin m → ℝ)
    (hP : convexHull ℝ (C : Set (Fin d → ℝ)) = {x | ∀ i, A i x ≤ b i})
    (v : Fin d → ℝ)
    (hv : v ∈ ({x | ∀ i, A i x ≤ b i} : Set (Fin d → ℝ)).extremePoints ℝ) :
    ∃ h : (Fin d → ℝ) →ₗ[ℝ] ℝ,
      (∀ x ∈ ({x | ∀ i, A i x ≤ b i} : Set (Fin d → ℝ)),
        x ≠ v → 0 < h (x - v)) ∧
      (∀ (y : Fin d → ℝ) (a : ℝ), 0 < a →
        ((∀ i, A i (v + (1 / a) • y) ≤ b i) ↔
          (∀ i, A i v = b i → A i y ≤ 0) ∧
          (∀ i, A i v < b i → A i y / (b i - A i v) ≤ a))) ∧
      (∀ y : Fin d → ℝ, h y = 1 → (∀ i, A i v = b i → A i y ≤ 0) →
        ∃ i : Fin m, A i v < b i ∧ 0 < A i y / (b i - A i v) ∧
          (∀ j, A j v < b j →
            A j y / (b j - A j v) ≤ A i y / (b i - A i v)) ∧
          ∀ a : ℝ, 0 < a →
            ((∀ j, A j (v + (1 / a) • y) ≤ b j) ↔
              A i y / (b i - A i v) ≤ a)) ∧
      (∀ x ∈ ({x | ∀ i, A i x ≤ b i} : Set (Fin d → ℝ)).extremePoints ℝ,
        x ≠ v →
        let y := (1 / h (x - v)) • (x - v)
        let a := 1 / h (x - v)
        h y = 1 ∧ v + (1 / a) • y = x ∧
          (∀ i, A i x = b i ↔ A i y = a * (b i - A i v)) ∧
          (∀ i, A i v < b i → A i y / (b i - A i v) ≤ a) ∧
          ∃ i, A i v < b i ∧ A i y / (b i - A i v) = a) ∧
      (∀ u w : Fin d → ℝ,
        u ∈ ({x | ∀ i, A i x ≤ b i} : Set (Fin d → ℝ)).extremePoints ℝ →
        w ∈ ({x | ∀ i, A i x ≤ b i} : Set (Fin d → ℝ)).extremePoints ℝ →
        u ≠ v → w ≠ v → u ≠ w →
        IsExposed ℝ {x : Fin d → ℝ | ∀ i, A i x ≤ b i} (segment ℝ u w) →
        ∃ i : Fin m, A i v < b i ∧ A i u = b i ∧ A i w = b i) ∧
      Set.InjOn (fun x => (1 / h (x - v)) • (x - v))
        (({x | ∀ i, A i x ≤ b i} : Set (Fin d → ℝ)).extremePoints ℝ \ {v}) := by
  classical
  have hv' : v ∈ (convexHull ℝ (C : Set (Fin d → ℝ))).extremePoints ℝ := by
    rw [hP]
    exact hv
  have hvC : v ∈ C := extremePoints_convexHull_subset hv'
  obtain ⟨h, hC⟩ := Hirsch.HullCoordinate.strict_vertex_functional C v hv'
  have hh := Hirsch.RadialRowEnvelope.strict_on_body C A b hP v h hC
  refine ⟨h, hh, ?_, ?_, ?_, ?_, ?_⟩
  · intro y a ha
    exact Hirsch.RadialRowEnvelope.epigraph_iff A b v hv.1 y a ha
  · intro y hy ht
    exact Hirsch.RadialRowEnvelope.ray_threshold C A b hP v hvC hv.1 h y hy ht
  · intro x hx hxv
    exact Hirsch.RadialRowEnvelope.vertex_envelope A b v x hv.1 hx hxv h
      (hh x hx.1 hxv)
  · intro u w hu hw huv hwv _huw hE
    exact Hirsch.RadialRowEnvelope.exposed_edge_row A b v u w hv.1 hu.1 hw.1 hE
      (Hirsch.RadialRowEnvelope.extreme_not_in_other_segment A b v u w hv hu.1 hw.1 huv hwv)
  · exact Hirsch.RadialRowEnvelope.vertex_injective A b v hv.1 h hh

#print axioms Hirsch.RadialRowEnvelope.epigraph_iff
#print axioms Hirsch.RadialRowEnvelope.strict_on_body
#print axioms Hirsch.RadialRowEnvelope.ray_threshold
#print axioms Hirsch.RadialRowEnvelope.non_target_active
#print axioms Hirsch.RadialRowEnvelope.vertex_envelope
#print axioms Hirsch.RadialRowEnvelope.vertex_injective
#print axioms Hirsch.RadialRowEnvelope.exposed_edge_row
#print axioms solution
