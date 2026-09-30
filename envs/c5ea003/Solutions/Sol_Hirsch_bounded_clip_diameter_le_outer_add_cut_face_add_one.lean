-- Prove2me | solution 1 for Hirsch.bounded_clip_diameter_le_outer_add_cut_face_add_one
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-07T02:46:41.90681+00:00
-- url     : https://prove2.me/submissions/470e3c1f-8bba-4357-aaaa-d1f59d1322bc

import Definitions.Def_Hirsch_model
import Mathlib
import Theorems.Thm_Hirsch_larman_bound

-- BEGIN Solutions/PolynomialHalfspaceEdge.lean

open scoped RealInnerProductSpace
open Set Hirsch

set_option maxHeartbeats 4000000

noncomputable section

namespace HirschCut

variable {d : ℕ}

lemma inner_combo (c p q : EuclideanSpace ℝ (Fin d)) (α β : ℝ) :
    ⟪c, α • p + β • q⟫ = α * ⟪c, p⟫ + β * ⟪c, q⟫ := by
  simp [inner_add_right, inner_smul_right]

/-- A retained old edge stays an edge after adding one halfspace. -/
lemma retained_edge
    (Q : Set (EuclideanSpace ℝ (Fin d)))
    (c : EuclideanSpace ℝ (Fin d)) (b : ℝ)
    {p q : EuclideanSpace ℝ (Fin d)} (hadj : Adj Q p q)
    (hp : ⟪c, p⟫ ≤ b) (hq : ⟪c, q⟫ ≤ b) :
    Adj (Q ∩ {x | ⟪c, x⟫ ≤ b}) p q := by
  refine ⟨hadj.1, hadj.2.mono Set.inter_subset_left ?_⟩
  intro x hx
  refine ⟨hadj.2.subset hx, ?_⟩
  obtain ⟨α, β, hα, hβ, hαβ, rfl⟩ := hx
  change ⟪c, α • p + β • q⟫ ≤ b
  rw [inner_combo]
  have h1 := mul_le_mul_of_nonneg_left hp hα
  have h2 := mul_le_mul_of_nonneg_left hq hβ
  have h3 : α * b + β * b = b := by rw [← add_mul, hαβ, one_mul]
  linarith

/-- The first part of an old edge crossing the cut plane is an edge of the
clipped polytope. Its new endpoint lies exactly on the cut plane. -/
lemma clip_crossing_edge
    (Q : Set (EuclideanSpace ℝ (Fin d)))
    (c : EuclideanSpace ℝ (Fin d)) (b : ℝ)
    {p q : EuclideanSpace ℝ (Fin d)} (hadj : Adj Q p q)
    (hp : ⟪c, p⟫ < b) (hq : b ≤ ⟪c, q⟫) :
    ∃ z : EuclideanSpace ℝ (Fin d), ⟪c, z⟫ = b ∧
      Adj (Q ∩ {x | ⟪c, x⟫ ≤ b}) p z := by
  let D : ℝ := ⟪c, q⟫ - ⟪c, p⟫
  have hD : 0 < D := by dsimp [D]; linarith
  let t : ℝ := (b - ⟪c, p⟫) / D
  have ht : 0 < t := div_pos (sub_pos.mpr hp) hD
  have ht1 : t ≤ 1 := by
    apply (div_le_iff₀ hD).2
    dsimp [D]
    linarith
  have htD : t * D = b - ⟪c, p⟫ := div_mul_cancel₀ _ hD.ne'
  let z : EuclideanSpace ℝ (Fin d) := (1 - t) • p + t • q
  have hz : ⟪c, z⟫ = b := by
    rw [show z = (1 - t) • p + t • q from rfl, inner_combo]
    dsimp [D] at htD
    nlinarith
  have hzseg : z ∈ segment ℝ p q :=
    ⟨1 - t, t, by linarith, ht.le, by ring, rfl⟩
  have heq : segment ℝ p z = {w | w ∈ segment ℝ p q ∧ ⟪c, w⟫ ≤ b} := by
    ext w
    constructor
    · intro hw
      have hwold : w ∈ segment ℝ p q :=
        (convex_segment p q).segment_subset (left_mem_segment ℝ p q) hzseg hw
      refine ⟨hwold, ?_⟩
      obtain ⟨α, β, hα, hβ, hαβ, rfl⟩ := hw
      rw [inner_combo, hz]
      have h1 := mul_le_mul_of_nonneg_left hp.le hα
      have h2 : α * b + β * b = b := by rw [← add_mul, hαβ, one_mul]
      linarith
    · rintro ⟨hw, hwb⟩
      obtain ⟨α, β, hα, hβ, hαβ, hcomb⟩ := hw
      have hαone : α = 1 - β := by linarith
      have hinner : ⟪c, w⟫ = ⟪c, p⟫ + β * D := by
        rw [← hcomb, inner_combo, hαone]
        dsimp [D]
        ring
      have hβt : β ≤ t := by
        rw [hinner] at hwb
        nlinarith
      let γ : ℝ := β / t
      have hγ0 : 0 ≤ γ := div_nonneg hβ ht.le
      have hγ1 : γ ≤ 1 := by
        apply (div_le_iff₀ ht).2
        linarith
      have hγt : γ * t = β := div_mul_cancel₀ _ ht.ne'
      have hflat : (1 - γ) • p + γ • z =
          (1 - γ * t) • p + (γ * t) • q := by
        dsimp [z]
        module
      refine ⟨1 - γ, γ, by linarith, hγ0, by ring, ?_⟩
      rw [hflat, hγt, ← hαone]
      exact hcomb
  have hpz : p ≠ z := by
    intro h
    exact hp.ne ((congrArg (fun x : EuclideanSpace ℝ (Fin d) => ⟪c, x⟫) h).trans hz)
  refine ⟨z, hz, hpz, ?_, ?_⟩
  · intro w hw
    rw [heq] at hw
    exact ⟨hadj.2.subset hw.1, hw.2⟩
  · intro x hx y hy w hw hop
    rw [heq] at hw ⊢
    exact ⟨hadj.2.left_mem_of_mem_openSegment hx.1 hy.1 hw.1 hop, hx.2⟩


end HirschCut
end


-- BEGIN Solutions/PolynomialHalfspaceVertex.lean

open scoped RealInnerProductSpace
open Set Hirsch

set_option maxHeartbeats 4000000

noncomputable section

namespace HirschCut

/-- A vertex strictly on the retained side of a cut was already a vertex of
 the convex outer set. New vertices created by one cut lie on its plane. -/
lemma strict_cut_extreme_to_parent {d : ℕ}
    (Q : Set (EuclideanSpace ℝ (Fin d))) (hconv : Convex ℝ Q)
    (c : EuclideanSpace ℝ (Fin d)) (b : ℝ)
    {u : EuclideanSpace ℝ (Fin d)}
    (hu : u ∈ extremePoints ℝ (Q ∩ {x | ⟪c, x⟫ ≤ b}))
    (hustrict : ⟪c, u⟫ < b) : u ∈ extremePoints ℝ Q := by
  refine ⟨hu.1.1, ?_⟩
  intro x hx y hy hopen
  obtain ⟨α, β, hα, hβ, hαβ, hcomb⟩ := hopen
  let Δ : ℝ := b - ⟪c, u⟫
  have hΔ : 0 < Δ := sub_pos.mpr hustrict
  let A : ℝ := ⟪c, x⟫ - ⟪c, u⟫
  let C : ℝ := ⟪c, y⟫ - ⟪c, u⟫
  let D : ℝ := Δ + |A| + |C| + 1
  have hD : 0 < D := by dsimp [D]; positivity
  have hΔD : Δ ≤ D := by
    dsimp [D]
    linarith [abs_nonneg A, abs_nonneg C]
  let ε : ℝ := Δ / D
  have hε : 0 < ε := div_pos hΔ hD
  have hε1 : ε ≤ 1 := by
    apply (div_le_iff₀ hD).2
    simpa only [one_mul] using hΔD
  have hεD : ε * D = Δ := div_mul_cancel₀ _ hD.ne'
  have hAD : A ≤ D := by
    have h := le_abs_self A
    dsimp [D]
    linarith [abs_nonneg C]
  have hCD : C ≤ D := by
    have h := le_abs_self C
    dsimp [D]
    linarith [abs_nonneg A]
  let x' : EuclideanSpace ℝ (Fin d) := (1 - ε) • u + ε • x
  let y' : EuclideanSpace ℝ (Fin d) := (1 - ε) • u + ε • y
  have hxQ : x' ∈ Q :=
    hconv hu.1.1 hx (by linarith) hε.le (by ring)
  have hyQ : y' ∈ Q :=
    hconv hu.1.1 hy (by linarith) hε.le (by ring)
  have hxcut : ⟪c, x'⟫ ≤ b := by
    have h := mul_le_mul_of_nonneg_left hAD hε.le
    rw [hεD] at h
    dsimp [x']
    rw [inner_add_right, inner_smul_right, inner_smul_right]
    dsimp [A, Δ] at h
    nlinarith
  have hycut : ⟪c, y'⟫ ≤ b := by
    have h := mul_le_mul_of_nonneg_left hCD hε.le
    rw [hεD] at h
    dsimp [y']
    rw [inner_add_right, inner_smul_right, inner_smul_right]
    dsimp [C, Δ] at h
    nlinarith
  have hopen' : u ∈ openSegment ℝ x' y' := by
    refine ⟨α, β, hα, hβ, hαβ, ?_⟩
    have hflat : α • x' + β • y' =
        (1 - ε) • u + ε • (α • x + β • y) := by
      dsimp [x', y']
      rw [show α = 1 - β by linarith]
      module
    rw [hflat, hcomb, ← add_smul]
    have hcoeff : (1 - ε) + ε = 1 := by ring
    rw [hcoeff, one_smul]
  have hxu : x' = u := hu.2 ⟨hxQ, hxcut⟩ ⟨hyQ, hycut⟩ hopen'
  have hzero : ε • (x - u) = 0 := by
    calc
      ε • (x - u) = x' - u := by dsimp [x']; module
      _ = 0 := sub_eq_zero.mpr hxu
  exact sub_eq_zero.mp ((smul_eq_zero.mp hzero).resolve_left hε.ne')


end HirschCut
end


-- BEGIN Solutions/PolynomialAdjEndpoints.lean

open scoped RealInnerProductSpace
open Set Hirsch

set_option maxHeartbeats 2000000

noncomputable section

namespace HirschPolynomialAccess

variable {d : ℕ}

/-- Both endpoints of an `Adj` edge are extreme points of the parent set.
`Adj` stores that the whole segment is an extreme subset; the endpoint fact is
an elementary consequence. -/
lemma adj_right_extreme
    (P : Set (EuclideanSpace ℝ (Fin d)))
    {u z : EuclideanSpace ℝ (Fin d)}
    (hadj : Adj P u z) : z ∈ extremePoints ℝ P := by
  rcases hadj with ⟨huz, hseg⟩
  have hzP : z ∈ P := hseg.subset (right_mem_segment ℝ u z)
  refine ⟨hzP, ?_⟩
  intro x hxP y hyP hzopen
  have hxseg : x ∈ segment ℝ u z :=
    hseg.left_mem_of_mem_openSegment hxP hyP (right_mem_segment ℝ u z) hzopen
  have hyseg : y ∈ segment ℝ u z :=
    hseg.right_mem_of_mem_openSegment hxP hyP (right_mem_segment ℝ u z) hzopen
  obtain ⟨a, b, ha, hb, hab, hx⟩ := hxseg
  obtain ⟨c, e, hc, he, hce, hy⟩ := hyseg
  obtain ⟨s, t, hs, ht, hst, hxy⟩ := hzopen
  have hcoeff : s * a + t * c + (s * b + t * e) = 1 := by
    calc
      s * a + t * c + (s * b + t * e) = s * (a + b) + t * (c + e) := by ring
      _ = s * 1 + t * 1 := by rw [hab, hce]
      _ = 1 := by linarith
  have hlin0 : s • x + t • y - z = 0 := sub_eq_zero.mpr hxy
  rw [← hx, ← hy] at hlin0
  have hrewrite :
      s • (a • u + b • z) + t • (c • u + e • z) - z =
        (s * a + t * c) • u + (s * b + t * e - 1) • z := by
    module
  have hlin1 :
      (s * a + t * c) • u + (s * b + t * e - 1) • z = 0 := by
    rw [← hrewrite]
    exact hlin0
  have hB : s * b + t * e - 1 = -(s * a + t * c) := by
    linarith [hcoeff]
  rw [hB] at hlin1
  have hlin : (s * a + t * c) • (u - z) = 0 := by
    rw [smul_sub, sub_eq_add_neg]
    simpa only [neg_smul] using hlin1
  have hcoef : s * a + t * c = 0 :=
    (smul_eq_zero.mp hlin).resolve_right (sub_ne_zero.mpr huz)
  have ha0 : a = 0 := by
    nlinarith [mul_nonneg ht.le hc]
  have hb1 : b = 1 := by linarith [hab]
  rw [ha0, zero_smul, zero_add, hb1, one_smul] at hx
  exact hx.symm

lemma adj_symm
    (P : Set (EuclideanSpace ℝ (Fin d)))
    {x y : EuclideanSpace ℝ (Fin d)}
    (h : Adj P x y) : Adj P y x := by
  refine ⟨h.1.symm, ?_⟩
  simpa [segment_symm] using h.2

lemma adj_left_extreme
    (P : Set (EuclideanSpace ℝ (Fin d)))
    {x y : EuclideanSpace ℝ (Fin d)}
    (h : Adj P x y) : x ∈ extremePoints ℝ P :=
  adj_right_extreme P (adj_symm P h)

end HirschPolynomialAccess
end


-- BEGIN Solutions/PolynomialProductWalk.lean

open Set Hirsch

set_option maxHeartbeats 4000000

noncomputable section

namespace HirschProduct

/-- Concatenate padded walks. This is independent of polytope geometry. -/
lemma append_walk {E : Type*} (R : E → E → Prop)
    {u v z : E} {A B : ℕ}
    (p q : ℕ → E)
    (hp0 : p 0 = u) (hpA : p A = v)
    (hq0 : q 0 = v) (hqB : q B = z)
    (hp : ∀ j < A, p j = p (j + 1) ∨ R (p j) (p (j + 1)))
    (hq : ∀ j < B, q j = q (j + 1) ∨ R (q j) (q (j + 1))) :
    ∃ w : ℕ → E, w 0 = u ∧ w (A + B) = z ∧
      ∀ j < A + B, w j = w (j + 1) ∨ R (w j) (w (j + 1)) := by
  let w : ℕ → E := fun j => if j < A then p j else q (j - A)
  have hleft (j : ℕ) (hj : j ≤ A) : w j = p j := by
    by_cases h : j < A
    · simp only [w, if_pos h]
    · have heq : j = A := by omega
      subst j
      simp only [w, lt_self_iff_false, if_false, Nat.sub_self, hq0, hpA]
  have hright (j : ℕ) (hj : A ≤ j) : w j = q (j - A) := by
    exact if_neg (by omega)
  refine ⟨w, (hleft 0 (Nat.zero_le A)).trans hp0, ?_, ?_⟩
  · rw [hright (A + B) (by omega), Nat.add_sub_cancel_left]
    exact hqB
  · intro j hj
    by_cases hjA : j < A
    · rw [hleft j (by omega), hleft (j + 1) (by omega)]
      exact hp j hjA
    · rw [hright j (by omega), hright (j + 1) (by omega)]
      have hidx : j + 1 - A = (j - A) + 1 := by omega
      rw [hidx]
      exact hq (j - A) (by omega)

lemma pad_walk {E : Type*} (R : E → E → Prop)
    {u v : E} {A B : ℕ} (hAB : A ≤ B)
    (w : ℕ → E) (h0 : w 0 = u) (hA : w A = v)
    (hs : ∀ j < A, w j = w (j + 1) ∨ R (w j) (w (j + 1))) :
    ∃ w' : ℕ → E, w' 0 = u ∧ w' B = v ∧
      ∀ j < B, w' j = w' (j + 1) ∨ R (w' j) (w' (j + 1)) := by
  let w' : ℕ → E := fun j => w (min j A)
  refine ⟨w', ?_, ?_, ?_⟩
  · simpa only [w', Nat.zero_min] using h0
  · simpa only [w', Nat.min_eq_right hAB] using hA
  · intro j hj
    by_cases hjA : j < A
    · have h0 : j ≤ A := by omega
      have h1 : j + 1 ≤ A := by omega
      simpa only [w', Nat.min_eq_left h0, Nat.min_eq_left h1] using hs j hjA
    · have h0 : A ≤ j := by omega
      have h1 : A ≤ j + 1 := by omega
      exact Or.inl (by simp only [w', Nat.min_eq_right h0, Nat.min_eq_right h1])

variable {ι : Type*} {E : ι → Type*}
variable [∀ i, AddCommGroup (E i)] [∀ i, Module ℝ (E i)]

/-- Moving one coordinate along a factor edge, with all other coordinates
fixed at factor vertices, gives a genuine edge of the Cartesian product. -/
lemma update_adj [DecidableEq ι]
    (P : ∀ i, Set (E i)) (base : ∀ i, E i) (i : ι)
    (hfix : ∀ j, j ≠ i → base j ∈ extremePoints ℝ (P j))
    {p q : E i} (hadj : Adj (P i) p q) :
    Adj (Set.univ.pi P) (Function.update base i p) (Function.update base i q) := by
  refine ⟨?_, ?_, ?_⟩
  · intro heq
    apply hadj.1
    simpa using congrFun heq i
  · intro z hz
    rw [← Pi.image_update_segment] at hz
    obtain ⟨t, ht, rfl⟩ := hz
    rw [Set.mem_univ_pi]
    intro j
    by_cases hji : j = i
    · subst j
      simpa using hadj.2.subset ht
    · simpa [Function.update_of_ne hji] using (hfix j hji).1
  · intro x hx y hy z hz hopen
    rw [Set.mem_univ_pi] at hx hy
    rw [← Pi.image_update_segment] at hz
    obtain ⟨t, ht, rfl⟩ := hz
    obtain ⟨α, β, hα, hβ, hαβ, hcomb⟩ := hopen
    have hop (j : ι) : Function.update base i t j ∈ openSegment ℝ (x j) (y j) :=
      ⟨α, β, hα, hβ, hαβ, congrFun hcomb j⟩
    have hti : t ∈ openSegment ℝ (x i) (y i) := by simpa using hop i
    have hxi : x i ∈ segment ℝ p q :=
      hadj.2.left_mem_of_mem_openSegment (hx i) (hy i) ht hti
    have hxfix (j : ι) (hji : j ≠ i) : x j = base j :=
      (hfix j hji).2 (hx j) (hy j) (by simpa [Function.update_of_ne hji] using hop j)
    rw [← Pi.image_update_segment]
    refine ⟨x i, hxi, ?_⟩
    funext j
    by_cases hji : j = i
    · subst j
      simp
    · simpa [Function.update_of_ne hji] using (hxfix j hji).symm

/-- A finite product has a diameter budget equal to the SUM of factor budgets.
The sum, rather than the total dimension, is the relevant routing quantity. -/
theorem diamLE_pi [Fintype ι]
    (P : ∀ i, Set (E i)) (B : ι → ℕ)
    (hD : ∀ i, DiamLE (P i) (B i)) :
    DiamLE (Set.univ.pi P) (∑ i, B i) := by
  classical
  have hwalk : ∀ s : Finset ι, ∀ u v : ∀ i, E i,
      (∀ i, u i ∈ extremePoints ℝ (P i)) →
      (∀ i, v i ∈ extremePoints ℝ (P i)) →
      (∀ i, i ∉ s → u i = v i) →
      ∃ w : ℕ → (∀ i, E i), w 0 = u ∧ w (∑ i ∈ s, B i) = v ∧
        ∀ j < ∑ i ∈ s, B i,
          w j = w (j + 1) ∨ Adj (Set.univ.pi P) (w j) (w (j + 1)) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        intro u v hu hv heq
        have huv : u = v := funext (fun i => heq i (by simp))
        subst v
        exact ⟨fun _ => u, rfl, rfl, fun _ _ => Or.inl rfl⟩
    | @insert i s his ih =>
        intro u v hu hv heq
        let mid : ∀ j, E j := Function.update u i (v i)
        have hm (j : ι) : mid j ∈ extremePoints ℝ (P j) := by
          by_cases hji : j = i
          · subst j
            simpa [mid] using hv i
          · simpa [mid, Function.update_of_ne hji] using hu j
        have hsame (j : ι) (hjs : j ∉ s) : mid j = v j := by
          by_cases hji : j = i
          · subst j
            simp [mid]
          · simpa [mid, Function.update_of_ne hji] using heq j (by simp [hji, hjs])
        obtain ⟨q, hq0, hqB, hqstep⟩ := ih mid v hm hv hsame
        obtain ⟨p, hp0, hpB, hpstep⟩ := hD i (u i) (hu i) (v i) (hv i)
        let wp : ℕ → (∀ j, E j) := fun t => Function.update u i (p t)
        have hwp0 : wp 0 = u := by simp [wp, hp0]
        have hwpB : wp (B i) = mid := by simp [wp, hpB, mid]
        have hwps : ∀ j < B i, wp j = wp (j + 1) ∨
            Adj (Set.univ.pi P) (wp j) (wp (j + 1)) := by
          intro j hj
          rcases hpstep j hj with h | h
          · exact Or.inl (congrArg (Function.update u i) h)
          · exact Or.inr (update_adj P u i (fun k _ => hu k) h)
        obtain ⟨w, hw0, hwB, hwstep⟩ :=
          append_walk (Adj (Set.univ.pi P)) wp q hwp0 hwpB hq0 hqB hwps hqstep
        refine ⟨w, hw0, ?_, ?_⟩
        · simpa only [Finset.sum_insert his] using hwB
        · simpa only [Finset.sum_insert his] using hwstep
  intro u hu v hv
  have hu' : ∀ i, u i ∈ extremePoints ℝ (P i) := by
    simpa only [extremePoints_pi, Set.mem_univ_pi] using hu
  have hv' : ∀ i, v i ∈ extremePoints ℝ (P i) := by
    simpa only [extremePoints_pi, Set.mem_univ_pi] using hv
  exact hwalk Finset.univ u v hu' hv' (fun i hi => False.elim (hi (Finset.mem_univ i)))


end HirschProduct
end


-- BEGIN Solutions/PolynomialClipWalk.lean

open scoped RealInnerProductSpace
open Set Hirsch HirschCut

set_option maxHeartbeats 4000000

noncomputable section

namespace HirschClip

abbrev Walk {E : Type*} [AddCommGroup E] [Module ℝ E]
    (P : Set E) (B : ℕ) (u v : E) : Prop :=
  ∃ w : ℕ → E, w 0 = u ∧ w B = v ∧
    ∀ j < B, w j = w (j + 1) ∨ Adj P (w j) (w (j + 1))

lemma adj_reverse {E : Type*} [AddCommGroup E] [Module ℝ E]
    {P : Set E} {u v : E} (h : Adj P u v) : Adj P v u := by
  refine ⟨Ne.symm h.1, ?_⟩
  simpa only [segment_symm] using h.2

lemma reverse_steps {E : Type*} [AddCommGroup E] [Module ℝ E]
    (P : Set E) {B : ℕ} (w : ℕ → E)
    (hs : ∀ j < B, w j = w (j + 1) ∨ Adj P (w j) (w (j + 1))) :
    ∀ j < B, w (B - j) = w (B - (j + 1)) ∨
      Adj P (w (B - j)) (w (B - (j + 1))) := by
  intro j hj
  have hi : B - (j + 1) < B := by omega
  have heq : B - (j + 1) + 1 = B - j := by omega
  rcases hs (B - (j + 1)) hi with h | h
  · exact Or.inl (by simpa only [heq] using h.symm)
  · exact Or.inr (by simpa only [heq] using adj_reverse h)

lemma walk_reverse {E : Type*} [AddCommGroup E] [Module ℝ E]
    {P : Set E} {B : ℕ} {u v : E} (h : Walk P B u v) : Walk P B v u := by
  obtain ⟨w, h0, hB, hs⟩ := h
  refine ⟨fun j => w (B - j), ?_, ?_, reverse_steps P w hs⟩
  · simpa only [Nat.sub_zero] using hB
  · simpa only [Nat.sub_self] using h0

lemma walk_append {E : Type*} [AddCommGroup E] [Module ℝ E]
    {P : Set E} {A B : ℕ} {u v z : E}
    (h1 : Walk P A u v) (h2 : Walk P B v z) : Walk P (A + B) u z := by
  obtain ⟨p, hp0, hpA, hp⟩ := h1
  obtain ⟨q, hq0, hqB, hq⟩ := h2
  exact HirschProduct.append_walk (Adj P) p q hp0 hpA hq0 hqB hp hq

lemma walk_pad {E : Type*} [AddCommGroup E] [Module ℝ E]
    {P : Set E} {A B : ℕ} {u v : E}
    (hAB : A ≤ B) (h : Walk P A u v) : Walk P B u v := by
  obtain ⟨w, h0, hA, hs⟩ := h
  exact HirschProduct.pad_walk (Adj P) hAB w h0 hA hs

variable {d : ℕ}

/-- The equality slice is an extreme subset of the retained halfspace. -/
lemma cut_face_isExtreme
    (Q : Set (EuclideanSpace ℝ (Fin d)))
    (c : EuclideanSpace ℝ (Fin d)) (b : ℝ) :
    IsExtreme ℝ (Q ∩ {x | ⟪c, x⟫ ≤ b}) (Q ∩ {x | ⟪c, x⟫ = b}) := by
  refine ⟨fun x hx => ⟨hx.1, hx.2.le⟩, ?_⟩
  intro x hx y hy z hz hop
  refine ⟨hx.1, ?_⟩
  obtain ⟨α, β, hα, hβ, hαβ, hcombo⟩ := hop
  have heq : α * ⟪c, x⟫ + β * ⟪c, y⟫ = b := by
    have h : ⟪c, z⟫ = b := hz.2
    rw [← hcombo, inner_combo] at h
    exact h
  have hxle : ⟪c, x⟫ ≤ b := hx.2
  have hyle : ⟪c, y⟫ ≤ b := hy.2
  have hweight : α * b + β * b = b := by
    rw [← add_mul, hαβ, one_mul]
  have hprod : α * (b - ⟪c, x⟫) = 0 := by
    nlinarith [mul_nonneg hα.le (sub_nonneg.mpr hxle),
      mul_nonneg hβ.le (sub_nonneg.mpr hyle)]
  have hslack := (mul_eq_zero.mp hprod).resolve_left hα.ne'
  exact (sub_eq_zero.mp hslack).symm

/-- A cut-face walk lifts to genuine retained-polytope edges. -/
lemma cut_face_walk
    (Q : Set (EuclideanSpace ℝ (Fin d)))
    (c : EuclideanSpace ℝ (Fin d)) (b : ℝ) (C : ℕ)
    (hF : DiamLE (Q ∩ {x | ⟪c, x⟫ = b}) C)
    {u v : EuclideanSpace ℝ (Fin d)}
    (hu : u ∈ extremePoints ℝ (Q ∩ {x | ⟪c, x⟫ ≤ b}))
    (hv : v ∈ extremePoints ℝ (Q ∩ {x | ⟪c, x⟫ ≤ b}))
    (huc : ⟪c, u⟫ = b) (hvc : ⟪c, v⟫ = b) :
    Walk (Q ∩ {x | ⟪c, x⟫ ≤ b}) C u v := by
  have huF : u ∈ extremePoints ℝ (Q ∩ {x | ⟪c, x⟫ = b}) := by
    refine ⟨⟨hu.1.1, huc⟩, ?_⟩
    intro p hp q hq hop
    exact hu.2 ⟨hp.1, hp.2.le⟩ ⟨hq.1, hq.2.le⟩ hop
  have hvF : v ∈ extremePoints ℝ (Q ∩ {x | ⟪c, x⟫ = b}) := by
    refine ⟨⟨hv.1.1, hvc⟩, ?_⟩
    intro p hp q hq hop
    exact hv.2 ⟨hp.1, hp.2.le⟩ ⟨hq.1, hq.2.le⟩ hop
  obtain ⟨w, h0, hC, hs⟩ := hF u huF v hvF
  refine ⟨w, h0, hC, ?_⟩
  intro j hj
  rcases hs j hj with h | h
  · exact Or.inl h
  · exact Or.inr ⟨h.1, (cut_face_isExtreme Q c b).trans h.2⟩

/-- Clip a prefix at its first contact, keeping its actual length k rather
than padding to the entire outer-walk budget. This permits two end portions
of the SAME outer walk to share one budget. -/
lemma clip_prefix
    (Q : Set (EuclideanSpace ℝ (Fin d)))
    (c : EuclideanSpace ℝ (Fin d)) (b : ℝ)
    (k : ℕ) (hk : 0 < k) (w : ℕ → EuclideanSpace ℝ (Fin d))
    (hbefore : ∀ l < k, ⟪c, w l⟫ < b)
    (hend : b ≤ ⟪c, w k⟫)
    (hstep : ∀ l < k, w l = w (l + 1) ∨ Adj Q (w l) (w (l + 1))) :
    ∃ z : EuclideanSpace ℝ (Fin d),
      z ∈ extremePoints ℝ (Q ∩ {x | ⟪c, x⟫ ≤ b}) ∧
      ⟪c, z⟫ = b ∧ Walk (Q ∩ {x | ⟪c, x⟫ ≤ b}) k (w 0) z := by
  let j := k - 1
  have hjk : j + 1 = k := by dsimp [j]; omega
  have hj : j < k := by omega
  have hleft := hbefore j hj
  have hright : b ≤ ⟪c, w (j + 1)⟫ := by simpa only [hjk] using hend
  have hedge : Adj Q (w j) (w (j + 1)) := by
    rcases hstep j hj with hsame | hadj
    · rw [hsame] at hleft
      exact False.elim ((not_lt_of_ge hright) hleft)
    · exact hadj
  obtain ⟨z, hcz, hzedge⟩ := clip_crossing_edge Q c b hedge hleft hright
  have hzext := HirschPolynomialAccess.adj_right_extreme _ hzedge
  let wp : ℕ → EuclideanSpace ℝ (Fin d) := fun l => if l < k then w l else z
  refine ⟨z, hzext, hcz, wp, ?_, ?_, ?_⟩
  · change (if 0 < k then w 0 else z) = w 0
    exact if_pos hk
  · change (if k < k then w k else z) = z
    exact if_neg (Nat.lt_irrefl k)
  · intro l hl
    by_cases hnext : l + 1 < k
    · rcases hstep l hl with hsame | hadj
      · exact Or.inl (by simpa only [wp, if_pos hl, if_pos hnext] using hsame)
      · have he := retained_edge Q c b hadj (hbefore l hl).le
          (hbefore (l + 1) hnext).le
        exact Or.inr (by simpa only [wp, if_pos hl, if_pos hnext] using he)
    · have hlj : l = j := by omega
      subst l
      exact Or.inr (by simpa only [wp, if_pos hj, if_neg hnext] using hzedge)

/-- An outer vertex strictly retained by the cut reaches the cut face within
B steps. This helper is derived from the variable-length prefix lemma. -/
lemma outer_cut_walk
    (Q : Set (EuclideanSpace ℝ (Fin d)))
    (c : EuclideanSpace ℝ (Fin d)) (b : ℝ) (B : ℕ)
    (hD : DiamLE Q B)
    {u v : EuclideanSpace ℝ (Fin d)}
    (hu : u ∈ extremePoints ℝ Q) (hv : v ∈ extremePoints ℝ Q)
    (huc : ⟪c, u⟫ < b) (hvc : b ≤ ⟪c, v⟫) :
    ∃ z : EuclideanSpace ℝ (Fin d),
      z ∈ extremePoints ℝ (Q ∩ {x | ⟪c, x⟫ ≤ b}) ∧
      ⟪c, z⟫ = b ∧ Walk (Q ∩ {x | ⟪c, x⟫ ≤ b}) B u z := by
  classical
  obtain ⟨w, hw0, hwB, hws⟩ := hD u hu v hv
  have hex : ∃ k : ℕ, k ≤ B ∧ b ≤ ⟪c, w k⟫ :=
    ⟨B, le_rfl, by simpa only [hwB] using hvc⟩
  let k := Nat.find hex
  have hk : k ≤ B ∧ b ≤ ⟪c, w k⟫ := Nat.find_spec hex
  have hkpos : 0 < k := by
    by_contra h
    have hk0 : k = 0 := by omega
    have hbad : b ≤ ⟪c, u⟫ := by simpa only [hk0, hw0] using hk.2
    exact (not_le_of_gt huc) hbad
  have hbefore : ∀ l < k, ⟪c, w l⟫ < b := by
    intro l hl
    by_contra h
    have hmin : k ≤ l := Nat.find_min' hex ⟨by omega, le_of_not_gt h⟩
    omega
  obtain ⟨z, hz, hcz, hwalk⟩ := clip_prefix Q c b k hkpos w hbefore hk.2
    (fun l hl => hws l (by omega))
  refine ⟨z, hz, hcz, ?_⟩
  apply walk_pad hk.1
  simpa only [hw0] using hwalk


end HirschClip
end


-- BEGIN Solutions/PolynomialClipSplice.lean

open scoped RealInnerProductSpace
open Set Hirsch HirschCut HirschClip

set_option maxHeartbeats 4000000

noncomputable section

namespace HirschClip

/-- Two strictly retained endpoints use one outer walk, not two independent
routes to the plane. Clip its first and last contacts and replace everything
between them by a cut-face walk. The total retained length is at most B. -/
theorem splice_outer_walk
    (d B C : ℕ) (Q : Set (EuclideanSpace ℝ (Fin d)))
    (c : EuclideanSpace ℝ (Fin d)) (b : ℝ)
    (hF : DiamLE (Q ∩ {x | ⟪c, x⟫ = b}) C)
    (w : ℕ → EuclideanSpace ℝ (Fin d))
    (hstart : ⟪c, w 0⟫ < b) (hfinish : ⟪c, w B⟫ < b)
    (hstep : ∀ j < B, w j = w (j + 1) ∨ Adj Q (w j) (w (j + 1))) :
    Walk (Q ∩ {x | ⟪c, x⟫ ≤ b}) (B + C) (w 0) (w B) := by
  classical
  by_cases hex : ∃ k : ℕ, k ≤ B ∧ b ≤ ⟪c, w k⟫
  · let k := Nat.find hex
    have hk : k ≤ B ∧ b ≤ ⟪c, w k⟫ := Nat.find_spec hex
    have hkpos : 0 < k := by
      by_contra h
      have hk0 : k = 0 := by omega
      have hbad : b ≤ ⟪c, w 0⟫ := by simpa only [hk0] using hk.2
      exact (not_le_of_gt hstart) hbad
    have hbefore : ∀ j < k, ⟪c, w j⟫ < b := by
      intro j hj
      by_contra h
      have hmin : k ≤ j := Nat.find_min' hex ⟨by omega, le_of_not_gt h⟩
      omega
    obtain ⟨p, hp, hcp, hwp⟩ := clip_prefix Q c b k hkpos w hbefore hk.2
      (fun j hj => hstep j (by omega))
    let wr : ℕ → EuclideanSpace ℝ (Fin d) := fun j => w (B - j)
    have hwr0 : wr 0 = w B := by simp only [wr, Nat.sub_zero]
    have hwrstep : ∀ j < B, wr j = wr (j + 1) ∨ Adj Q (wr j) (wr (j + 1)) :=
      reverse_steps Q w hstep
    have hexr : ∃ l : ℕ, l ≤ B - k ∧ b ≤ ⟪c, wr l⟫ := by
      refine ⟨B - k, le_rfl, ?_⟩
      have hidx : B - (B - k) = k := by omega
      simpa only [wr, hidx] using hk.2
    let l := Nat.find hexr
    have hl : l ≤ B - k ∧ b ≤ ⟪c, wr l⟫ := Nat.find_spec hexr
    have hlpos : 0 < l := by
      by_contra h
      have hl0 : l = 0 := by omega
      have hbad : b ≤ ⟪c, w B⟫ := by simpa only [hl0, hwr0] using hl.2
      exact (not_le_of_gt hfinish) hbad
    have hbeforer : ∀ j < l, ⟪c, wr j⟫ < b := by
      intro j hj
      by_contra h
      have hmin : l ≤ j := Nat.find_min' hexr ⟨by omega, le_of_not_gt h⟩
      omega
    obtain ⟨q, hq, hcq, hwq⟩ := clip_prefix Q c b l hlpos wr hbeforer hl.2
      (fun j hj => hwrstep j (by omega))
    have hqp : Walk (Q ∩ {x | ⟪c, x⟫ ≤ b}) l q (w B) := by
      simpa only [hwr0] using walk_reverse hwq
    have hmiddle := cut_face_walk Q c b C hF hp hq hcp hcq
    have hspliced := walk_append (walk_append hwp hmiddle) hqp
    exact walk_pad (by omega : k + C + l ≤ B + C) hspliced
  · have hle : ∀ j ≤ B, ⟪c, w j⟫ ≤ b := by
      intro j hj
      have hn : ¬ b ≤ ⟪c, w j⟫ := fun h => hex ⟨j, hj, h⟩
      exact (lt_of_not_ge hn).le
    have hretained : Walk (Q ∩ {x | ⟪c, x⟫ ≤ b}) B (w 0) (w B) := by
      refine ⟨w, rfl, rfl, ?_⟩
      intro j hj
      rcases hstep j hj with h | h
      · exact Or.inl h
      · exact Or.inr (retained_edge Q c b h (hle j (by omega)) (hle (j + 1) (by omega)))
    exact walk_pad (Nat.le_add_right B C) hretained


end HirschClip
end


-- BEGIN Solutions/PolynomialUnboundedCutCore.lean

open scoped RealInnerProductSpace
open Set Hirsch HirschCut HirschClip

set_option maxHeartbeats 4000000

noncomputable section

namespace HirschUnboundedCut

lemma one_edge_walk {E : Type*} [AddCommGroup E] [Module ℝ E]
    {P : Set E} {u v : E} (h : Adj P u v) : Walk P 1 u v := by
  refine ⟨fun j => if j = 0 then u else v, by simp, by simp, ?_⟩
  intro j hj
  have hj0 : j = 0 := by omega
  subst j
  simpa using Or.inr h

variable {d : ℕ}

/-- If every outer vertex is retained, every outer graph walk is retained.
There is no boundedness or compactness hypothesis on the outer set. -/
lemma retain_outer_walk
    (Q : Set (EuclideanSpace ℝ (Fin d)))
    (c : EuclideanSpace ℝ (Fin d)) (b : ℝ)
    (hall : ∀ y ∈ extremePoints ℝ Q, ⟪c, y⟫ ≤ b)
    {B : ℕ} {u v : EuclideanSpace ℝ (Fin d)}
    (hw : Walk Q B u v) :
    Walk (Q ∩ {x | ⟪c, x⟫ ≤ b}) B u v := by
  obtain ⟨w, h0, hB, hs⟩ := hw
  refine ⟨w, h0, hB, ?_⟩
  intro j hj
  rcases hs j hj with heq | he
  · exact Or.inl heq
  · exact Or.inr (retained_edge Q c b he
      (hall _ (HirschPolynomialAccess.adj_left_extreme Q he))
      (hall _ (HirschPolynomialAccess.adj_right_extreme Q he)))

/-- A clipped walk from a strict vertex to the plane has a last strict edge.
Only existence of the walk is used; its length will subsequently be discarded. -/
lemma first_plane_edge
    (Q : Set (EuclideanSpace ℝ (Fin d)))
    (c : EuclideanSpace ℝ (Fin d)) (b : ℝ)
    {D : ℕ} {u v : EuclideanSpace ℝ (Fin d)}
    (huc : ⟪c, u⟫ < b) (hvc : ⟪c, v⟫ = b)
    (hw : Walk (Q ∩ {x | ⟪c, x⟫ ≤ b}) D u v) :
    ∃ x z : EuclideanSpace ℝ (Fin d),
      x ∈ extremePoints ℝ (Q ∩ {y | ⟪c, y⟫ ≤ b}) ∧
      z ∈ extremePoints ℝ (Q ∩ {y | ⟪c, y⟫ ≤ b}) ∧
      ⟪c, x⟫ < b ∧ ⟪c, z⟫ = b ∧
      Adj (Q ∩ {y | ⟪c, y⟫ ≤ b}) x z := by
  classical
  obtain ⟨w, h0, hD, hs⟩ := hw
  have hex : ∃ k : ℕ, k ≤ D ∧ ⟪c, w k⟫ = b :=
    ⟨D, le_rfl, by simpa only [hD] using hvc⟩
  let k := Nat.find hex
  have hk : k ≤ D ∧ ⟪c, w k⟫ = b := Nat.find_spec hex
  have hk0 : k ≠ 0 := by
    intro h
    have heq : ⟪c, u⟫ = b := by simpa only [h, h0] using hk.2
    exact (ne_of_lt huc) heq
  let j := k - 1
  have hjk : j + 1 = k := by dsimp [j]; omega
  have hjD : j < D := by omega
  have hjnot : ⟪c, w j⟫ ≠ b := by
    intro hjplane
    have hmin : k ≤ j := Nat.find_min' hex ⟨by omega, hjplane⟩
    omega
  have hedge : Adj (Q ∩ {y | ⟪c, y⟫ ≤ b}) (w j) (w k) := by
    rcases hs j hjD with heq | he
    · have hwjk : w j = w k := by simpa only [hjk] using heq
      exact False.elim (hjnot (hwjk ▸ hk.2))
    · simpa only [hjk] using he
  have hx := HirschPolynomialAccess.adj_left_extreme _ hedge
  have hz := HirschPolynomialAccess.adj_right_extreme _ hedge
  exact ⟨w j, w k, hx, hz, lt_of_le_of_ne hx.1.2 hjnot, hk.2, hedge⟩

/-- No exterior outer vertex is needed if a clipped path to the face exists.
The cost is at most one extra edge. If an outer vertex lies on/beyond the
plane, ordinary clipping gives B; otherwise all outer edges survive and a
B-step outer path to the last strict predecessor is followed by one edge. -/
theorem cut_access_of_outer_diameter_and_path
    (Q : Set (EuclideanSpace ℝ (Fin d))) (hconv : Convex ℝ Q)
    (c : EuclideanSpace ℝ (Fin d)) (b : ℝ) (B : ℕ)
    (hQ : DiamLE Q B)
    {D : ℕ} {u v : EuclideanSpace ℝ (Fin d)}
    (hu : u ∈ extremePoints ℝ (Q ∩ {x | ⟪c, x⟫ ≤ b}))
    (hvc : ⟪c, v⟫ = b)
    (hw : Walk (Q ∩ {x | ⟪c, x⟫ ≤ b}) D u v) :
    ∃ z : EuclideanSpace ℝ (Fin d),
      z ∈ extremePoints ℝ (Q ∩ {x | ⟪c, x⟫ ≤ b}) ∧
      ⟪c, z⟫ = b ∧ Walk (Q ∩ {x | ⟪c, x⟫ ≤ b}) (B + 1) u z := by
  classical
  by_cases huc : ⟪c, u⟫ = b
  · exact ⟨u, hu, huc, ⟨fun _ => u, rfl, rfl, fun _ _ => Or.inl rfl⟩⟩
  have hult : ⟪c, u⟫ < b := lt_of_le_of_ne hu.1.2 huc
  have huQ := strict_cut_extreme_to_parent Q hconv c b hu hult
  by_cases hex : ∃ y ∈ extremePoints ℝ Q, b ≤ ⟪c, y⟫
  · obtain ⟨y, hy, hyc⟩ := hex
    obtain ⟨z, hz, hzc, hwz⟩ := outer_cut_walk Q c b B hQ huQ hy hult hyc
    exact ⟨z, hz, hzc, walk_pad (by omega : B ≤ B + 1) hwz⟩
  · have hall : ∀ y ∈ extremePoints ℝ Q, ⟪c, y⟫ ≤ b := by
      intro y hy
      exact (lt_of_not_ge (fun h => hex ⟨y, hy, h⟩)).le
    obtain ⟨x, z, hx, hz, hxc, hzc, hxz⟩ := first_plane_edge Q c b hult hvc hw
    have hxQ := strict_cut_extreme_to_parent Q hconv c b hx hxc
    have hux := retain_outer_walk Q c b hall (hQ u huQ x hxQ)
    exact ⟨z, hz, hzc, walk_append hux (one_edge_walk hxz)⟩

/-- Full clipped diameter with a possibly unbounded outer set. Connectivity
of the clipped graph supplies a crossing witness, not a numerical budget.
Two strict endpoints still share ONE outer walk, by first/last-contact
splicing. Thus the bound is B+C+1, not 2B+C+2. -/
theorem clipped_diameter_of_outer_and_connected_clip
    (Q : Set (EuclideanSpace ℝ (Fin d))) (hconv : Convex ℝ Q)
    (c : EuclideanSpace ℝ (Fin d)) (b : ℝ) (B C : ℕ)
    (hQ : DiamLE Q B)
    (hF : DiamLE (Q ∩ {x | ⟪c, x⟫ = b}) C)
    (hconnect : ∀ u ∈ extremePoints ℝ (Q ∩ {x | ⟪c, x⟫ ≤ b}),
      ∀ v ∈ extremePoints ℝ (Q ∩ {x | ⟪c, x⟫ ≤ b}),
        ∃ D : ℕ, Walk (Q ∩ {x | ⟪c, x⟫ ≤ b}) D u v) :
    DiamLE (Q ∩ {x | ⟪c, x⟫ ≤ b}) (B + C + 1) := by
  intro u hu v hv
  by_cases huc : ⟪c, u⟫ = b
  · by_cases hvc : ⟪c, v⟫ = b
    · exact walk_pad (by omega : C ≤ B + C + 1)
        (cut_face_walk Q c b C hF hu hv huc hvc)
    · obtain ⟨D, hvu⟩ := hconnect v hv u hu
      obtain ⟨z, hz, hzc, hvz⟩ :=
        cut_access_of_outer_diameter_and_path Q hconv c b B hQ hv huc hvu
      have hzu := cut_face_walk Q c b C hF hz hu hzc huc
      exact walk_pad (by omega : (B + 1) + C ≤ B + C + 1)
        (walk_reverse (walk_append hvz hzu))
  · have hult : ⟪c, u⟫ < b := lt_of_le_of_ne hu.1.2 huc
    have huQ := strict_cut_extreme_to_parent Q hconv c b hu hult
    by_cases hvc : ⟪c, v⟫ = b
    · obtain ⟨D, huv⟩ := hconnect u hu v hv
      obtain ⟨z, hz, hzc, huz⟩ :=
        cut_access_of_outer_diameter_and_path Q hconv c b B hQ hu hvc huv
      exact walk_pad (by omega : (B + 1) + C ≤ B + C + 1)
        (walk_append huz (cut_face_walk Q c b C hF hz hv hzc hvc))
    · have hvlt : ⟪c, v⟫ < b := lt_of_le_of_ne hv.1.2 hvc
      have hvQ := strict_cut_extreme_to_parent Q hconv c b hv hvlt
      obtain ⟨w, h0, hB, hs⟩ := hQ u huQ v hvQ
      have hstart : ⟪c, w 0⟫ < b := by simpa only [h0] using hult
      have hfinish : ⟪c, w B⟫ < b := by simpa only [hB] using hvlt
      have hspliced := splice_outer_walk d B C Q c b hF w hstart hfinish hs
      apply walk_pad (by omega : B + C ≤ B + C + 1)
      simpa only [h0, hB] using hspliced


end HirschUnboundedCut
end


-- BEGIN Solutions/PolynomialUnboundedCutHpoly.lean

open scoped RealInnerProductSpace
open Set Hirsch HirschCut HirschClip

set_option maxHeartbeats 4000000

noncomputable section

namespace HirschUnboundedCut

variable {d n : ℕ}

lemma hpoly_convex
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) :
    Convex ℝ (Hpoly a b) := by
  intro x hx y hy α β hα hβ hαβ i
  change ⟪a i, α • x + β • y⟫ ≤ b i
  rw [inner_combo]
  calc
    α * ⟪a i, x⟫ + β * ⟪a i, y⟫ ≤ α * b i + β * b i :=
      add_le_add (mul_le_mul_of_nonneg_left (hx i) hα)
        (mul_le_mul_of_nonneg_left (hy i) hβ)
    _ = b i := by rw [← add_mul, hαβ, one_mul]

/-- A bounded clipped H-polyhedron has a connected vertex graph even if the
outer H-polyhedron is unbounded. Larman is applied only to the n+1-row clip;
its numerical bound is used for existence and discarded by the routing core. -/
lemma bounded_hpoly_clip_connected
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (c : EuclideanSpace ℝ (Fin d)) (β : ℝ)
    (hbd : Bornology.IsBounded (Hpoly a b ∩ {x | ⟪c, x⟫ ≤ β}))
    (u : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (Hpoly a b ∩ {x | ⟪c, x⟫ ≤ β}))
    (v : EuclideanSpace ℝ (Fin d))
    (hv : v ∈ extremePoints ℝ (Hpoly a b ∩ {x | ⟪c, x⟫ ≤ β})) :
    ∃ D : ℕ, Walk (Hpoly a b ∩ {x | ⟪c, x⟫ ≤ β}) D u v := by
  let a' : Fin (n + 1) → EuclideanSpace ℝ (Fin d) := Fin.lastCases c a
  let b' : Fin (n + 1) → ℝ := Fin.lastCases β b
  have hclip : Hpoly a' b' = Hpoly a b ∩ {x | ⟪c, x⟫ ≤ β} := by
    ext x
    constructor
    · intro hx
      refine ⟨?_, ?_⟩
      · intro i
        simpa [a', b'] using hx i.castSucc
      · simpa [a', b'] using hx (Fin.last n)
    · rintro ⟨hx, hcut⟩ i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa [a', b'] using hcut
      · simpa [a', b'] using hx j
  have hne' : (Hpoly a' b').Nonempty := by
    rw [hclip]
    exact ⟨u, hu.1⟩
  have hbd' : Bornology.IsBounded (Hpoly a' b') := by rwa [hclip]
  have hdiam := Hirsch.larman_bound d (n + 1) a' b' hne' hbd'
  rw [hclip] at hdiam
  exact ⟨(n + 1) * 2 ^ (d - 3), hdiam u hu v hv⟩

end HirschUnboundedCut
end


-- BEGIN Solutions/PolynomialUnboundedCutDiameterSubmission.lean

open scoped RealInnerProductSpace
open Set Hirsch HirschClip HirschUnboundedCut

set_option maxHeartbeats 4000000

noncomputable section

/-- A bounded clip of a possibly unbounded H-polyhedron has diameter at most
outer vertex-graph diameter plus cut-face diameter plus one. Empty clips and
zero normals are allowed. The two assumed numerical bounds are not derived
from row count, so this is not an unrestricted polynomial Hirsch theorem. -/
theorem solution
    (d n B C : ℕ)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (c : EuclideanSpace ℝ (Fin d)) (β : ℝ)
    (hbd : Bornology.IsBounded (Hpoly a b ∩ {x | ⟪c, x⟫ ≤ β}))
    (hQ : DiamLE (Hpoly a b) B)
    (hF : DiamLE (Hpoly a b ∩ {x | ⟪c, x⟫ = β}) C) :
    DiamLE (Hpoly a b ∩ {x | ⟪c, x⟫ ≤ β}) (B + C + 1) := by
  apply clipped_diameter_of_outer_and_connected_clip
    (Hpoly a b) (hpoly_convex a b) c β B C hQ hF
  intro u hu v hv
  exact bounded_hpoly_clip_connected a b c β hbd u hu v hv

end


#print axioms solution
