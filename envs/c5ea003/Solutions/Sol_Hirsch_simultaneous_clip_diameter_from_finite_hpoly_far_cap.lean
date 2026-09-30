-- Prove2me | solution 1 for Hirsch.simultaneous_clip_diameter_from_finite_hpoly_far_cap
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-10T14:55:07.428974+00:00
-- url     : https://prove2.me/submissions/5c71657b-14bf-4b9b-b474-55a91422c8d7

import Definitions.Def_Hirsch_model
import Mathlib

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


end HirschUnboundedCut
end


-- BEGIN Solutions/PolynomialHpolyRecessionCap.lean

/-! Algebraic recession lemmas for the canonical far-cap functional of a finite
H-polyhedron. These are the finite-row ingredients needed before formalizing
compact far-cap existence. -/

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

noncomputable section
namespace HirschHpolyCap

variable {d n : ℕ}

/-- Directions which preserve every defining halfspace when followed forward. -/
def RecessionDir (a : Fin n → EuclideanSpace ℝ (Fin d))
    (r : EuclideanSpace ℝ (Fin d)) : Prop :=
  ∀ i, ⟪a i, r⟫ ≤ 0

/-- The canonical cap normal: the negative sum of all H-row normals. -/
def capNormal (a : Fin n → EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) :=
  -∑ i, a i

/-- A recession direction really does generate a feasible forward ray from
any feasible H-polyhedron point. -/
lemma ray_mem_hpoly
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    {x r : EuclideanSpace ℝ (Fin d)}
    (hx : x ∈ Hpoly a b) (hr : RecessionDir a r) {t : ℝ} (ht : 0 ≤ t) :
    x + t • r ∈ Hpoly a b := by
  intro i
  change ⟪a i, x + t • r⟫ ≤ b i
  rw [inner_add_right, inner_smul_right]
  have htr : t * ⟪a i, r⟫ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht (hr i)
  linarith [hx i]

/-- If a direction and its opposite are both recession directions, every H-row
normal annihilates that direction. -/
lemma recession_and_neg_iff_common_kernel
    (a : Fin n → EuclideanSpace ℝ (Fin d))
    (r : EuclideanSpace ℝ (Fin d)) :
    RecessionDir a r ∧ RecessionDir a (-r) ↔ ∀ i, ⟪a i, r⟫ = 0 := by
  constructor
  · rintro ⟨hr, hneg⟩ i
    have h1 := hr i
    have h2 := hneg i
    rw [inner_neg_right] at h2
    linarith
  · intro h
    constructor
    · intro i
      rw [h i]
    · intro i
      rw [inner_neg_right, h i, neg_zero]

/-- The canonical cap functional is nondecreasing along every recession ray. -/
lemma capNormal_nonneg_on_recession
    (a : Fin n → EuclideanSpace ℝ (Fin d))
    {r : EuclideanSpace ℝ (Fin d)} (hr : RecessionDir a r) :
    0 ≤ ⟪capNormal a, r⟫ := by
  have hsum : ∑ i, ⟪a i, r⟫ ≤ 0 := by
    simpa using Finset.sum_nonpos fun i _ => hr i
  have hsumInner : ⟪∑ i, a i, r⟫ = ∑ i, ⟪a i, r⟫ := by
    simpa using (sum_inner (Finset.univ : Finset (Fin n)) a r)
  rw [capNormal, inner_neg_left, hsumInner]
  linarith

/-- Under the no-line/common-kernel condition, the canonical cap functional is
strictly positive on every nonzero recession direction. -/
lemma capNormal_pos_on_nonzero_recession
    (a : Fin n → EuclideanSpace ℝ (Fin d))
    (hkernel : ∀ r : EuclideanSpace ℝ (Fin d),
      (∀ i, ⟪a i, r⟫ = 0) → r = 0)
    {r : EuclideanSpace ℝ (Fin d)} (hr : RecessionDir a r) (hr0 : r ≠ 0) :
    0 < ⟪capNormal a, r⟫ := by
  have hex : ∃ i, ⟪a i, r⟫ < 0 := by
    by_contra h
    push_neg at h
    have hz : ∀ i, ⟪a i, r⟫ = 0 := fun i => le_antisymm (hr i) (h i)
    exact hr0 (hkernel r hz)
  obtain ⟨i, hi⟩ := hex
  have hsum_le : ∑ j, ⟪a j, r⟫ ≤ 0 := by
    simpa using Finset.sum_nonpos fun j _ => hr j
  have hsum_ne : (∑ j, ⟪a j, r⟫) ≠ 0 := by
    intro hzero
    have hall : ∀ j ∈ (Finset.univ : Finset (Fin n)), ⟪a j, r⟫ = 0 :=
      (Finset.sum_eq_zero_iff_of_nonpos (fun j _ => hr j)).mp (by simpa using hzero)
    exact hi.ne (hall i (Finset.mem_univ i))
  have hsum : ∑ j, ⟪a j, r⟫ < 0 := lt_of_le_of_ne hsum_le hsum_ne
  have hsumInner : ⟪∑ j, a j, r⟫ = ∑ j, ⟪a j, r⟫ := by
    simpa using (sum_inner (Finset.univ : Finset (Fin n)) a r)
  rw [capNormal, inner_neg_left, hsumInner]
  linarith

/-- The no-common-kernel condition is equivalent to excluding nonzero line
directions from the finite halfspace recession system. -/
lemma no_common_kernel_iff_no_recession_line
    (a : Fin n → EuclideanSpace ℝ (Fin d)) :
    (∀ r : EuclideanSpace ℝ (Fin d), (∀ i, ⟪a i, r⟫ = 0) → r = 0) ↔
      ∀ r : EuclideanSpace ℝ (Fin d),
        RecessionDir a r → RecessionDir a (-r) → r = 0 := by
  constructor
  · intro hk r hr hn
    exact hk r ((recession_and_neg_iff_common_kernel a r).mp ⟨hr, hn⟩)
  · intro h r hz
    have hp := (recession_and_neg_iff_common_kernel a r).mpr hz
    exact h r hp.1 hp.2


end HirschHpolyCap
end


-- BEGIN Solutions/PolynomialHpolyFarCapCompact.lean

/-! Compactness of the canonical far cap for a finite pointed H-polyhedron.
The proof embeds the ambient space by all row evaluations. The common-kernel
condition makes this a closed embedding; the original upper inequalities plus
one cap inequality give two-sided coordinate bounds in the image. -/

open scoped BigOperators RealInnerProductSpace
open Set Hirsch Topology

noncomputable section
namespace HirschHpolyCap

variable {d n : ℕ}

def rowMap (a : Fin n → EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) →ₗ[ℝ] (Fin n → ℝ) where
  toFun := fun x i => ⟪a i, x⟫
  map_add' := by
    intro x y
    ext i
    simp [inner_add_right]
  map_smul' := by
    intro c x
    ext i
    simp [inner_smul_right]

@[simp] lemma rowMap_apply
    (a : Fin n → EuclideanSpace ℝ (Fin d))
    (x : EuclideanSpace ℝ (Fin d)) (i : Fin n) :
    rowMap a x i = ⟪a i, x⟫ := rfl

def rowLower (b : Fin n → ℝ) (T : ℝ) (i : Fin n) : ℝ :=
  -T - (Finset.univ.erase i).sum b

def cappedHpoly
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) (T : ℝ) :
    Set (EuclideanSpace ℝ (Fin d)) :=
  Hpoly a b ∩ {x | ⟪capNormal a, x⟫ ≤ T}

lemma rowMap_ker_eq_bot
    (a : Fin n → EuclideanSpace ℝ (Fin d))
    (hkernel : ∀ r : EuclideanSpace ℝ (Fin d),
      (∀ i, ⟪a i, r⟫ = 0) → r = 0) :
    LinearMap.ker (rowMap a) = ⊥ := by
  rw [LinearMap.ker_eq_bot]
  intro x y hxy
  have hdiff : x - y = 0 := hkernel (x - y) (by
    intro i
    have hi : ⟪a i, x⟫ = ⟪a i, y⟫ := congrFun hxy i
    rw [inner_sub_right, hi, sub_self])
  exact sub_eq_zero.mp hdiff

lemma rowMap_isClosedEmbedding
    (a : Fin n → EuclideanSpace ℝ (Fin d))
    (hkernel : ∀ r : EuclideanSpace ℝ (Fin d),
      (∀ i, ⟪a i, r⟫ = 0) → r = 0) :
    IsClosedEmbedding (rowMap a) := by
  exact LinearMap.isClosedEmbedding_of_injective (rowMap_ker_eq_bot a hkernel)

lemma capped_row_bounds
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) (T : ℝ)
    {x : EuclideanSpace ℝ (Fin d)}
    (hx : x ∈ cappedHpoly a b T) :
    rowMap a x ∈ Set.Icc (rowLower b T) b := by
  rcases hx with ⟨hxH, hxcap⟩
  change ⟪capNormal a, x⟫ ≤ T at hxcap
  constructor
  · intro i
    have hsumInner : ⟪∑ j, a j, x⟫ = ∑ j, ⟪a j, x⟫ := by
      simpa using (sum_inner (Finset.univ : Finset (Fin n)) a x)
    have hsumEval : -T ≤ ∑ j, ⟪a j, x⟫ := by
      rw [capNormal, inner_neg_left, hsumInner] at hxcap
      linarith
    have hother :
        (Finset.univ.erase i).sum (fun j => ⟪a j, x⟫) ≤
          (Finset.univ.erase i).sum b := by
      exact Finset.sum_le_sum fun j _ => hxH j
    have hsplit :
        (Finset.univ.erase i).sum (fun j => ⟪a j, x⟫) + ⟪a i, x⟫ =
          ∑ j, ⟪a j, x⟫ := by
      exact Finset.univ.sum_erase_add (fun j => ⟪a j, x⟫) (Finset.mem_univ i)
    change rowLower b T i ≤ ⟪a i, x⟫
    rw [rowLower]
    linarith
  · intro i
    exact hxH i

lemma cappedHpoly_isClosed
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) (T : ℝ) :
    IsClosed (cappedHpoly a b T) := by
  have hH : IsClosed (Hpoly a b) := by
    change IsClosed {x : EuclideanSpace ℝ (Fin d) | ∀ i, ⟪a i, x⟫ ≤ b i}
    rw [show {x : EuclideanSpace ℝ (Fin d) | ∀ i, ⟪a i, x⟫ ≤ b i} =
        ⋂ i, {x | ⟪a i, x⟫ ≤ b i} by ext x; simp]
    exact isClosed_iInter fun i =>
      isClosed_le (continuous_const.inner continuous_id) continuous_const
  have hcap : IsClosed {x : EuclideanSpace ℝ (Fin d) | ⟪capNormal a, x⟫ ≤ T} :=
    isClosed_le (continuous_const.inner continuous_id) continuous_const
  exact hH.inter hcap

/-- A finite H-polyhedron with no common row kernel becomes compact after
intersecting it with the canonical summed-normal cap halfspace. -/
theorem cappedHpoly_isCompact
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) (T : ℝ)
    (hkernel : ∀ r : EuclideanSpace ℝ (Fin d),
      (∀ i, ⟪a i, r⟫ = 0) → r = 0) :
    IsCompact (cappedHpoly a b T) := by
  let K : Set (Fin n → ℝ) := Set.Icc (rowLower b T) b
  have hK : IsCompact K := isCompact_Icc
  have hpre : IsCompact ((rowMap a) ⁻¹' K) :=
    (rowMap_isClosedEmbedding a hkernel).isCompact_preimage hK
  apply hpre.of_isClosed_subset (cappedHpoly_isClosed a b T)
  intro x hx
  exact capped_row_bounds a b T hx


end HirschHpolyCap
end


-- BEGIN Solutions/PolynomialHpolyFarCapPreserve.lean

/-! Preservation of old H-polyhedron vertices and edges under a cap halfspace. -/

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

noncomputable section
namespace HirschHpolyCap

variable {d n : ℕ}

lemma segment_mem_cap_of_endpoints
    (c : EuclideanSpace ℝ (Fin d)) (T : ℝ)
    {x y : EuclideanSpace ℝ (Fin d)}
    (hx : ⟪c, x⟫ ≤ T) (hy : ⟪c, y⟫ ≤ T) :
    segment ℝ x y ⊆ {z | ⟪c, z⟫ ≤ T} := by
  rintro z ⟨α, β, hα, hβ, hab, rfl⟩
  change ⟪c, α • x + β • y⟫ ≤ T
  rw [inner_add_right, inner_smul_right, inner_smul_right]
  have hx' : α * ⟪c, x⟫ ≤ α * T := mul_le_mul_of_nonneg_left hx hα
  have hy' : β * ⟪c, y⟫ ≤ β * T := mul_le_mul_of_nonneg_left hy hβ
  calc
    α * ⟪c, x⟫ + β * ⟪c, y⟫ ≤ α * T + β * T := add_le_add hx' hy'
    _ = (α + β) * T := by ring
    _ = T := by rw [hab, one_mul]

/-- An old extreme vertex satisfying the cap inequality remains an extreme
vertex after capping. -/
lemma old_vertex_survives_cap
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) (T : ℝ)
    {x : EuclideanSpace ℝ (Fin d)}
    (hx : x ∈ extremePoints ℝ (Hpoly a b))
    (hcap : ⟪capNormal a, x⟫ ≤ T) :
    x ∈ extremePoints ℝ (cappedHpoly a b T) := by
  apply inter_extremePoints_subset_extremePoints_of_subset inter_subset_left
  exact ⟨⟨hx.1, hcap⟩, hx⟩

/-- An old edge whose endpoints satisfy the cap inequality survives as the same
edge of the capped H-polyhedron. -/
lemma old_edge_survives_cap
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) (T : ℝ)
    {x y : EuclideanSpace ℝ (Fin d)}
    (hxy : Adj (Hpoly a b) x y)
    (hx : ⟪capNormal a, x⟫ ≤ T) (hy : ⟪capNormal a, y⟫ ≤ T) :
    Adj (cappedHpoly a b T) x y := by
  refine ⟨hxy.1, hxy.2.mono inter_subset_left ?_⟩
  intro z hz
  exact ⟨hxy.2.subset hz, segment_mem_cap_of_endpoints (capNormal a) T hx hy hz⟩


end HirschHpolyCap
end


-- BEGIN Solutions/PolynomialHpolyVertexConverse.lean

/-! Converse to the active-row spanning lemma: if the active H-rows at a
feasible point annihilate only the zero direction, then the point is extreme. -/

open scoped RealInnerProductSpace
open Set Hirsch

namespace HirschHpolyCap

variable {d n : ℕ}

lemma extreme_of_tight_rows_separate
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x : EuclideanSpace ℝ (Fin d)) (hx : x ∈ Hpoly a b)
    (hsep : ∀ y : EuclideanSpace ℝ (Fin d),
      (∀ i, ⟪a i, x⟫ = b i → ⟪a i, y⟫ = 0) → y = 0) :
    x ∈ extremePoints ℝ (Hpoly a b) := by
  refine ⟨hx, ?_⟩
  intro p hp q hq hop
  have hpx : p - x = 0 := hsep (p - x) (by
    intro i hi
    obtain ⟨α, β, hα, hβ, hab, hcomb⟩ := hop
    have hp_i := hp i
    have hq_i := hq i
    have hx_combo : ⟪a i, x⟫ = α * ⟪a i, p⟫ + β * ⟪a i, q⟫ := by
      rw [← hcomb, inner_add_right, inner_smul_right, inner_smul_right]
    have hip : ⟪a i, p⟫ = b i := by
      apply le_antisymm hp_i
      by_contra hnot
      have hp_lt : ⟪a i, p⟫ < b i := lt_of_not_ge hnot
      have hp_mul : α * ⟪a i, p⟫ < α * b i := mul_lt_mul_of_pos_left hp_lt hα
      have hq_mul : β * ⟪a i, q⟫ ≤ β * b i :=
        mul_le_mul_of_nonneg_left hq_i hβ.le
      have hsum : α * ⟪a i, p⟫ + β * ⟪a i, q⟫ < α * b i + β * b i :=
        add_lt_add_of_lt_of_le hp_mul hq_mul
      have hright : α * b i + β * b i = b i := by
        calc
          α * b i + β * b i = (α + β) * b i := by ring
          _ = b i := by rw [hab, one_mul]
      have hcontra : b i < b i := by
        calc
          b i = ⟪a i, x⟫ := hi.symm
          _ = α * ⟪a i, p⟫ + β * ⟪a i, q⟫ := hx_combo
          _ < α * b i + β * b i := hsum
          _ = b i := hright
      exact (lt_irrefl (b i)) hcontra
    rw [inner_sub_right, hip, hi, sub_self])
  exact sub_eq_zero.mp hpx


end HirschHpolyCap

-- BEGIN Solutions/PolynomialHpolyHorizonKernel.lean

/-! Local linear structure at a new horizon vertex of the canonical H-polyhedron
cap. The old active rows have a common kernel of dimension at most one, because
adding the active cap functional makes the point extreme. -/

open scoped RealInnerProductSpace
open Set Hirsch

noncomputable section
namespace HirschHpolyCap

variable {d n : ℕ}

/-- At a horizon vertex, a direction annihilating every active old row and the
cap normal must be zero. -/
lemma horizon_active_rows_separate
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) (T : ℝ)
    (x : EuclideanSpace ℝ (Fin d))
    (hx : x ∈ extremePoints ℝ (cappedHpoly a b T))
    (horizon : ⟪capNormal a, x⟫ = T)
    (y : EuclideanSpace ℝ (Fin d))
    (hold : ∀ i, ⟪a i, x⟫ = b i → ⟪a i, y⟫ = 0)
    (hcap : ⟪capNormal a, y⟫ = 0) :
    y = 0 := by
  classical
  have hlocal : ∀ i : Fin n, ∃ t : ℝ,
      0 < t ∧ t * |⟪a i, y⟫| ≤ b i - ⟪a i, x⟫ := by
    intro i
    by_cases hi : ⟪a i, x⟫ = b i
    · refine ⟨1, zero_lt_one, ?_⟩
      rw [hold i hi, abs_zero, mul_zero, hi, sub_self]
    · have hs : 0 < b i - ⟪a i, x⟫ :=
        sub_pos.mpr (lt_of_le_of_ne (hx.1.1 i) hi)
      have hd : 0 < |⟪a i, y⟫| + 1 := by positivity
      let t : ℝ := (b i - ⟪a i, x⟫) / (|⟪a i, y⟫| + 1)
      have ht : 0 < t := div_pos hs hd
      have hprod : t * (|⟪a i, y⟫| + 1) = b i - ⟪a i, x⟫ := by
        dsimp [t]
        exact div_mul_cancel₀ _ (ne_of_gt hd)
      exact ⟨t, ht, by nlinarith⟩
  choose e hepos hebound using hlocal
  have huniform : ∀ S : Finset (Fin n), ∃ t : ℝ,
      0 < t ∧ ∀ i ∈ S, t ≤ e i := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact ⟨1, zero_lt_one, by simp⟩
    | @insert i S hi ih =>
      obtain ⟨t, ht, hti⟩ := ih
      refine ⟨min (e i) t, lt_min (hepos i) ht, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with hji | hjS
      · subst j
        exact min_le_left _ _
      · exact (min_le_right _ _).trans (hti j hjS)
  obtain ⟨t, ht, hte⟩ := huniform Finset.univ
  have hbudget : ∀ i, t * |⟪a i, y⟫| ≤ b i - ⟪a i, x⟫ := by
    intro i
    exact (mul_le_mul_of_nonneg_right (hte i (Finset.mem_univ i))
      (abs_nonneg _)).trans (hebound i)
  have hpH : x + t • y ∈ Hpoly a b := by
    intro i
    have hmul := mul_le_mul_of_nonneg_left (le_abs_self ⟪a i, y⟫) ht.le
    rw [inner_add_right, inner_smul_right]
    linarith [hbudget i]
  have hmH : x - t • y ∈ Hpoly a b := by
    intro i
    have hmul := mul_le_mul_of_nonneg_left (neg_le_abs ⟪a i, y⟫) ht.le
    rw [mul_neg] at hmul
    rw [inner_sub_right, inner_smul_right]
    linarith [hbudget i]
  have hpCap : ⟪capNormal a, x + t • y⟫ ≤ T := by
    rw [inner_add_right, inner_smul_right, hcap, mul_zero, add_zero, horizon]
  have hmCap : ⟪capNormal a, x - t • y⟫ ≤ T := by
    rw [inner_sub_right, inner_smul_right, hcap, mul_zero, sub_zero, horizon]
  have hp : x + t • y ∈ cappedHpoly a b T := ⟨hpH, hpCap⟩
  have hm : x - t • y ∈ cappedHpoly a b T := ⟨hmH, hmCap⟩
  have hmid : x ∈ openSegment ℝ (x + t • y) (x - t • y) := by
    refine ⟨(1 / 2 : ℝ), (1 / 2 : ℝ), by norm_num, by norm_num,
      by norm_num, ?_⟩
    module
  have hpeq : x + t • y = x := hx.2 hp hm hmid
  have hty : t • y = 0 := by
    have h := congrArg (fun z => z - x) hpeq
    simpa using h
  exact (smul_eq_zero.mp hty).resolve_left (ne_of_gt ht)

/-- Any chosen nonzero old-active kernel direction spans the whole old-active
kernel at a horizon vertex. -/
lemma horizon_old_active_kernel_spanned
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) (T : ℝ)
    (x : EuclideanSpace ℝ (Fin d))
    (hx : x ∈ extremePoints ℝ (cappedHpoly a b T))
    (horizon : ⟪capNormal a, x⟫ = T)
    (r : EuclideanSpace ℝ (Fin d)) (hr0 : r ≠ 0)
    (hr : ∀ i, ⟪a i, x⟫ = b i → ⟪a i, r⟫ = 0)
    (y : EuclideanSpace ℝ (Fin d))
    (hy : ∀ i, ⟪a i, x⟫ = b i → ⟪a i, y⟫ = 0) :
    ∃ c : ℝ, y = c • r := by
  have hcr : ⟪capNormal a, r⟫ ≠ 0 := by
    intro hz
    exact hr0 (horizon_active_rows_separate a b T x hx horizon r hr hz)
  let c : ℝ := ⟪capNormal a, y⟫ / ⟪capNormal a, r⟫
  have hwOld : ∀ i, ⟪a i, x⟫ = b i → ⟪a i, y - c • r⟫ = 0 := by
    intro i hi
    rw [inner_sub_right, inner_smul_right, hy i hi, hr i hi, mul_zero, sub_zero]
  have hwCap : ⟪capNormal a, y - c • r⟫ = 0 := by
    rw [inner_sub_right, inner_smul_right]
    dsimp [c]
    field_simp
    ring
  have hw := horizon_active_rows_separate a b T x hx horizon (y - c • r) hwOld hwCap
  exact ⟨c, sub_eq_zero.mp hw⟩

/-- Once one additional old row is nonzero on the one-dimensional horizon
kernel, adjoining that row to the old active rows separates all directions. -/
lemma horizon_old_active_plus_row_separate
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) (T : ℝ)
    (x : EuclideanSpace ℝ (Fin d))
    (hx : x ∈ extremePoints ℝ (cappedHpoly a b T))
    (horizon : ⟪capNormal a, x⟫ = T)
    (r : EuclideanSpace ℝ (Fin d)) (hr0 : r ≠ 0)
    (hr : ∀ i, ⟪a i, x⟫ = b i → ⟪a i, r⟫ = 0)
    (j : Fin n) (hrj : ⟪a j, r⟫ ≠ 0)
    (y : EuclideanSpace ℝ (Fin d))
    (hy : ∀ i, ⟪a i, x⟫ = b i → ⟪a i, y⟫ = 0)
    (hyj : ⟪a j, y⟫ = 0) :
    y = 0 := by
  obtain ⟨c, rfl⟩ := horizon_old_active_kernel_spanned a b T x hx horizon r hr0 hr y hy
  have hc : c = 0 := by
    rw [inner_smul_right] at hyj
    exact (mul_eq_zero.mp hyj).resolve_right hrj
  simp [hc]


end HirschHpolyCap
end


-- BEGIN Solutions/PolynomialHpolyHorizonInward.lean

/-! A genuinely new horizon vertex has a nonzero inward direction which
annihilates all old active rows, and at least one previously inactive old row
increases along that direction. -/

open scoped RealInnerProductSpace
open Set Hirsch

noncomputable section
namespace HirschHpolyCap

variable {d n : ℕ}

lemma exists_inward_old_active_direction
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) (T : ℝ)
    (x : EuclideanSpace ℝ (Fin d))
    (hx : x ∈ extremePoints ℝ (cappedHpoly a b T))
    (horizon : ⟪capNormal a, x⟫ = T)
    (hnotold : x ∉ extremePoints ℝ (Hpoly a b)) :
    ∃ r : EuclideanSpace ℝ (Fin d),
      r ≠ 0 ∧
      (∀ i, ⟪a i, x⟫ = b i → ⟪a i, r⟫ = 0) ∧
      ⟪capNormal a, r⟫ < 0 := by
  have hex : ∃ r : EuclideanSpace ℝ (Fin d),
      r ≠ 0 ∧ (∀ i, ⟪a i, x⟫ = b i → ⟪a i, r⟫ = 0) := by
    by_contra hnone
    have hsep : ∀ y : EuclideanSpace ℝ (Fin d),
        (∀ i, ⟪a i, x⟫ = b i → ⟪a i, y⟫ = 0) → y = 0 := by
      intro y hy
      by_contra hy0
      exact hnone ⟨y, hy0, hy⟩
    exact hnotold (extreme_of_tight_rows_separate a b x hx.1.1 hsep)
  obtain ⟨r, hr0, hr⟩ := hex
  have hcr0 : ⟪capNormal a, r⟫ ≠ 0 := by
    intro hz
    exact hr0 (horizon_active_rows_separate a b T x hx horizon r hr hz)
  by_cases hneg : ⟪capNormal a, r⟫ < 0
  · exact ⟨r, hr0, hr, hneg⟩
  · have hpos : 0 < ⟪capNormal a, r⟫ := lt_of_le_of_ne (le_of_not_gt hneg) hcr0.symm
    refine ⟨-r, neg_ne_zero.mpr hr0, ?_, ?_⟩
    · intro i hi
      rw [inner_neg_right, hr i hi, neg_zero]
    · rw [inner_neg_right]
      linarith

lemma inward_direction_has_increasing_old_row
    (a : Fin n → EuclideanSpace ℝ (Fin d))
    {r : EuclideanSpace ℝ (Fin d)}
    (hin : ⟪capNormal a, r⟫ < 0) :
    ∃ i, 0 < ⟪a i, r⟫ := by
  by_contra h
  push Not at h
  have hr : RecessionDir a r := fun i => h i
  exact (not_lt_of_ge (capNormal_nonneg_on_recession a hr)) hin

lemma exists_increasing_inactive_row_at_new_horizon
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) (T : ℝ)
    (x : EuclideanSpace ℝ (Fin d))
    (hx : x ∈ extremePoints ℝ (cappedHpoly a b T))
    (horizon : ⟪capNormal a, x⟫ = T)
    (hnotold : x ∉ extremePoints ℝ (Hpoly a b)) :
    ∃ r : EuclideanSpace ℝ (Fin d), ∃ i : Fin n,
      r ≠ 0 ∧
      (∀ j, ⟪a j, x⟫ = b j → ⟪a j, r⟫ = 0) ∧
      ⟪capNormal a, r⟫ < 0 ∧
      0 < ⟪a i, r⟫ ∧
      ⟪a i, x⟫ < b i := by
  obtain ⟨r, hr0, hr, hcap⟩ :=
    exists_inward_old_active_direction a b T x hx horizon hnotold
  obtain ⟨i, hi⟩ := inward_direction_has_increasing_old_row a hcap
  have hix : ⟪a i, x⟫ < b i := by
    have hle := hx.1.1 i
    exact lt_of_le_of_ne hle (fun heq => (lt_irrefl 0) (by simpa [hr i heq] using hi))
  exact ⟨r, i, hr0, hr, hcap, hi, hix⟩


end HirschHpolyCap
end


-- BEGIN Solutions/PolynomialHpolyHorizonFirstHit.lean

/-! Follow the one-dimensional inward horizon direction until the first old
H-inequality becomes tight. The first-hit point is an old H-polyhedron vertex. -/

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

noncomputable section
namespace HirschHpolyCap

variable {d n : ℕ}

/-- A genuinely new horizon vertex admits a positive first-hit time along an
inward old-active-kernel direction. The result exposes one attaining old row,
so the segment can subsequently be certified as an actual cap edge. -/
theorem new_horizon_first_hit_old_vertex
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) (T : ℝ)
    (x : EuclideanSpace ℝ (Fin d))
    (hx : x ∈ extremePoints ℝ (cappedHpoly a b T))
    (horizon : ⟪capNormal a, x⟫ = T)
    (hnotold : x ∉ extremePoints ℝ (Hpoly a b)) :
    ∃ r : EuclideanSpace ℝ (Fin d), ∃ t : ℝ, ∃ j : Fin n,
      r ≠ 0 ∧ 0 < t ∧
      (∀ i, ⟪a i, x⟫ = b i → ⟪a i, r⟫ = 0) ∧
      ⟪capNormal a, r⟫ < 0 ∧
      0 < ⟪a j, r⟫ ∧
      ⟪a j, x + t • r⟫ = b j ∧
      x + t • r ∈ extremePoints ℝ (Hpoly a b) ∧
      ⟪capNormal a, x + t • r⟫ < T := by
  classical
  obtain ⟨r, i0, hr0, hrActive, hrCap, hi0, hxi0⟩ :=
    exists_increasing_inactive_row_at_new_horizon a b T x hx horizon hnotold
  let S : Finset (Fin n) := Finset.univ.filter (fun i => 0 < ⟪a i, r⟫)
  have hi0S : i0 ∈ S := by simp [S, hi0]
  have hS : S.Nonempty := ⟨i0, hi0S⟩
  let τ : Fin n → ℝ := fun i => (b i - ⟪a i, x⟫) / ⟪a i, r⟫
  let times : Finset ℝ := S.image τ
  have htimes : times.Nonempty := Finset.image_nonempty.mpr hS
  let t : ℝ := times.min' htimes
  have htmem : t ∈ times := Finset.min'_mem times htimes
  obtain ⟨j, hjS, hjt⟩ := Finset.mem_image.mp htmem
  have hjpos : 0 < ⟪a j, r⟫ := by simpa [S] using hjS
  have hjstrict : ⟪a j, x⟫ < b j := by
    have hle := hx.1.1 j
    exact lt_of_le_of_ne hle (fun heq => by
      have hz := hrActive j heq
      linarith)
  have hτj : 0 < τ j := div_pos (sub_pos.mpr hjstrict) hjpos
  have htpos : 0 < t := by
    rw [← hjt]
    exact hτj
  have htle : ∀ i ∈ S, t ≤ τ i := by
    intro i hiS
    exact Finset.min'_le times (τ i) (Finset.mem_image_of_mem τ hiS)
  let y := x + t • r
  have hyH : y ∈ Hpoly a b := by
    intro i
    change ⟪a i, x + t • r⟫ ≤ b i
    rw [inner_add_right, inner_smul_right]
    by_cases hipos : 0 < ⟪a i, r⟫
    · have hiS : i ∈ S := by simp [S, hipos]
      have hti := htle i hiS
      dsimp [τ] at hti
      have hmul := (le_div_iff₀ hipos).mp hti
      linarith
    · have hir : ⟪a i, r⟫ ≤ 0 := le_of_not_gt hipos
      have hprod : t * ⟪a i, r⟫ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos htpos.le hir
      linarith [hx.1.1 i]
  have hjhit : ⟪a j, y⟫ = b j := by
    change ⟪a j, x + t • r⟫ = b j
    rw [inner_add_right, inner_smul_right]
    have htj : t = τ j := by exact hjt.symm
    rw [htj]
    dsimp [τ]
    field_simp
    ring
  have hOldTightAtY : ∀ i, ⟪a i, x⟫ = b i → ⟪a i, y⟫ = b i := by
    intro i hi
    change ⟪a i, x + t • r⟫ = b i
    rw [inner_add_right, inner_smul_right, hrActive i hi, mul_zero, add_zero, hi]
  have hyExtreme : y ∈ extremePoints ℝ (Hpoly a b) := by
    apply extreme_of_tight_rows_separate a b y hyH
    intro z hz
    apply horizon_old_active_plus_row_separate a b T x hx horizon r hr0 hrActive j hjpos.ne' z
    · intro i hi
      exact hz i (hOldTightAtY i hi)
    · exact hz j hjhit
  have hyCap : ⟪capNormal a, y⟫ < T := by
    change ⟪capNormal a, x + t • r⟫ < T
    rw [inner_add_right, inner_smul_right, horizon]
    have : t * ⟪capNormal a, r⟫ < 0 := mul_neg_of_pos_of_neg htpos hrCap
    linarith
  exact ⟨r, t, j, hr0, htpos, hrActive, hrCap, hjpos, hjhit,
    hyExtreme, hyCap⟩


end HirschHpolyCap
end


-- BEGIN Solutions/PolynomialHpolyHorizonEdge.lean

/-! The first-hit segment from a genuinely new horizon vertex is an actual edge
of the capped H-polyhedron. -/

open scoped RealInnerProductSpace
open Set Hirsch

noncomputable section
namespace HirschHpolyCap

variable {d n : ℕ}

/-- If `r` spans the old-active kernel at a horizon vertex, moving a positive
time `t` inward reaches an old row `j` for the first time, and the resulting
point is feasible, then the segment between the endpoints is an extreme
one-dimensional face of the cap. -/
lemma first_hit_segment_adjacent
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) (T : ℝ)
    (x r : EuclideanSpace ℝ (Fin d)) (t : ℝ) (j : Fin n)
    (hx : x ∈ extremePoints ℝ (cappedHpoly a b T))
    (horizon : ⟪capNormal a, x⟫ = T)
    (hr0 : r ≠ 0) (ht : 0 < t)
    (hrActive : ∀ i, ⟪a i, x⟫ = b i → ⟪a i, r⟫ = 0)
    (hrCap : ⟪capNormal a, r⟫ < 0)
    (hjpos : 0 < ⟪a j, r⟫)
    (hyH : x + t • r ∈ Hpoly a b)
    (hjhit : ⟪a j, x + t • r⟫ = b j) :
    Adj (cappedHpoly a b T) (x + t • r) x := by
  let y := x + t • r
  have hyCapStrict : ⟪capNormal a, y⟫ < T := by
    dsimp [y]
    rw [inner_add_right, inner_smul_right, horizon]
    have hprod : t * ⟪capNormal a, r⟫ < 0 := mul_neg_of_pos_of_neg ht hrCap
    linarith
  have hy : y ∈ cappedHpoly a b T := ⟨hyH, hyCapStrict.le⟩
  have hy_ne_x : y ≠ x := by
    intro h
    have htr : t • r = 0 := by
      have hh := congrArg (fun z => z - x) h
      simpa [y] using hh
    exact hr0 ((smul_eq_zero.mp htr).resolve_left ht.ne')
  refine ⟨hy_ne_x, ?_⟩
  constructor
  · intro z hz
    obtain ⟨α, β, hα, hβ, hab, rfl⟩ := hz
    constructor
    · intro i
      have hyi := hyH i
      have hxi := hx.1.1 i
      change ⟪a i, α • y + β • x⟫ ≤ b i
      rw [inner_add_right, inner_smul_right, inner_smul_right]
      have hy' : α * ⟪a i, y⟫ ≤ α * b i := mul_le_mul_of_nonneg_left hyi hα
      have hx' : β * ⟪a i, x⟫ ≤ β * b i := mul_le_mul_of_nonneg_left hxi hβ
      calc
        α * ⟪a i, y⟫ + β * ⟪a i, x⟫ ≤ α * b i + β * b i := add_le_add hy' hx'
        _ = (α + β) * b i := by ring
        _ = b i := by rw [hab, one_mul]
    · change ⟪capNormal a, α • y + β • x⟫ ≤ T
      rw [inner_add_right, inner_smul_right, inner_smul_right]
      have hy' : α * ⟪capNormal a, y⟫ ≤ α * T :=
        mul_le_mul_of_nonneg_left hyCapStrict.le hα
      have hx' : β * ⟪capNormal a, x⟫ ≤ β * T :=
        mul_le_mul_of_nonneg_left hx.1.2 hβ
      calc
        α * ⟪capNormal a, y⟫ + β * ⟪capNormal a, x⟫ ≤ α * T + β * T :=
          add_le_add hy' hx'
        _ = (α + β) * T := by ring
        _ = T := by rw [hab, one_mul]
  · intro p hp q hq w hwseg hwopen
    have hOldTightY : ∀ i, ⟪a i, x⟫ = b i → ⟪a i, y⟫ = b i := by
      intro i hi
      dsimp [y]
      rw [inner_add_right, inner_smul_right, hrActive i hi, mul_zero, add_zero, hi]
    have hOldTightW : ∀ i, ⟪a i, x⟫ = b i → ⟪a i, w⟫ = b i := by
      intro i hi
      obtain ⟨α, β, hα, hβ, hab, hw⟩ := hwseg
      rw [← hw, inner_add_right, inner_smul_right, inner_smul_right,
        hOldTightY i hi, hi]
      calc
        α * b i + β * b i = (α + β) * b i := by ring
        _ = b i := by rw [hab, one_mul]
    have hOldTightP : ∀ i, ⟪a i, x⟫ = b i → ⟪a i, p⟫ = b i := by
      intro i hi
      obtain ⟨α, β, hα, hβ, hab, hw⟩ := hwopen
      have hp_i := hp.1 i
      have hq_i := hq.1 i
      have havg : b i = α * ⟪a i, p⟫ + β * ⟪a i, q⟫ := by
        rw [← hOldTightW i hi, ← hw, inner_add_right, inner_smul_right, inner_smul_right]
      apply le_antisymm hp_i
      by_contra hnot
      have hp_lt : ⟪a i, p⟫ < b i := lt_of_not_ge hnot
      have hp_mul : α * ⟪a i, p⟫ < α * b i := mul_lt_mul_of_pos_left hp_lt hα
      have hq_mul : β * ⟪a i, q⟫ ≤ β * b i :=
        mul_le_mul_of_nonneg_left hq_i hβ.le
      have hsum : α * ⟪a i, p⟫ + β * ⟪a i, q⟫ < α * b i + β * b i :=
        add_lt_add_of_lt_of_le hp_mul hq_mul
      have hright : α * b i + β * b i = b i := by
        calc
          α * b i + β * b i = (α + β) * b i := by ring
          _ = b i := by rw [hab, one_mul]
      have hcontra : b i < b i := by
        calc
          b i = α * ⟪a i, p⟫ + β * ⟪a i, q⟫ := havg
          _ < α * b i + β * b i := hsum
          _ = b i := hright
      exact (lt_irrefl (b i)) hcontra
    obtain ⟨c, hpc⟩ := horizon_old_active_kernel_spanned
      a b T x hx horizon r hr0 hrActive (p - x) (by
        intro i hi
        rw [inner_sub_right, hOldTightP i hi, hi, sub_self])
    have hpform : p = x + c • r := by
      have hpform' : p = c • r + x := sub_eq_iff_eq_add.mp hpc
      simpa [add_comm] using hpform'
    have hc0 : 0 ≤ c := by
      have hpcap := hp.2
      change ⟪capNormal a, p⟫ ≤ T at hpcap
      rw [hpform, inner_add_right, inner_smul_right, horizon] at hpcap
      have hmul : c * ⟪capNormal a, r⟫ ≤ 0 := by linarith
      by_contra hc
      have hcneg : c < 0 := lt_of_not_ge hc
      have hpos : 0 < c * ⟪capNormal a, r⟫ := mul_pos_of_neg_of_neg hcneg hrCap
      exact (not_lt_of_ge hmul) hpos
    have hct : c ≤ t := by
      have hpj := hp.1 j
      have hyj : ⟪a j, y⟫ = b j := by simpa [y] using hjhit
      rw [hpform, inner_add_right, inner_smul_right] at hpj
      dsimp [y] at hyj
      rw [inner_add_right, inner_smul_right] at hyj
      have hmul : c * ⟪a j, r⟫ ≤ t * ⟪a j, r⟫ := by linarith
      exact le_of_mul_le_mul_right hmul hjpos
    let γ : ℝ := c / t
    have hγ0 : 0 ≤ γ := div_nonneg hc0 ht.le
    have hγ1 : γ ≤ 1 := (div_le_one ht).2 hct
    have hγt : γ * t = c := div_mul_cancel₀ c ht.ne'
    refine ⟨γ, 1 - γ, hγ0, by linarith, by ring, ?_⟩
    calc
      γ • y + (1 - γ) • x = x + (γ * t) • r := by
        dsimp [y]
        module
      _ = x + c • r := by rw [hγt]
      _ = p := hpform.symm


end HirschHpolyCap
end


-- BEGIN Solutions/PolynomialHpolyHorizonClassify.lean

/-! Complete local classification of vertices of the canonical capped finite
H-polyhedron: every cap vertex is old, or is on the horizon and adjacent to an
old H-polyhedron vertex. -/

open scoped RealInnerProductSpace
open Set Hirsch

noncomputable section
namespace HirschHpolyCap

variable {d n : ℕ}

lemma hpoly_convex
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) :
    Convex ℝ (Hpoly a b) := by
  intro x hx y hy α β hα hβ hab
  intro i
  change ⟪a i, α • x + β • y⟫ ≤ b i
  rw [inner_add_right, inner_smul_right, inner_smul_right]
  have hx' : α * ⟪a i, x⟫ ≤ α * b i := mul_le_mul_of_nonneg_left (hx i) hα
  have hy' : β * ⟪a i, y⟫ ≤ β * b i := mul_le_mul_of_nonneg_left (hy i) hβ
  calc
    α * ⟪a i, x⟫ + β * ⟪a i, y⟫ ≤ α * b i + β * b i := add_le_add hx' hy'
    _ = (α + β) * b i := by ring
    _ = b i := by rw [hab, one_mul]

/-- A genuinely new horizon cap vertex is adjacent, in the capped graph, to an
old H-polyhedron vertex reached by the finite first-hit construction. -/
theorem new_horizon_adjacent_old_vertex
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) (T : ℝ)
    (x : EuclideanSpace ℝ (Fin d))
    (hx : x ∈ extremePoints ℝ (cappedHpoly a b T))
    (horizon : ⟪capNormal a, x⟫ = T)
    (hnotold : x ∉ extremePoints ℝ (Hpoly a b)) :
    ∃ y, y ∈ extremePoints ℝ (Hpoly a b) ∧
      Adj (cappedHpoly a b T) y x := by
  obtain ⟨r, t, j, hr0, ht, hrActive, hrCap, hjpos, hjhit, hyOld, hyCap⟩ :=
    new_horizon_first_hit_old_vertex a b T x hx horizon hnotold
  let y := x + t • r
  have hadj : Adj (cappedHpoly a b T) y x :=
    first_hit_segment_adjacent a b T x r t j hx horizon hr0 ht hrActive hrCap
      hjpos hyOld.1 hjhit
  exact ⟨y, hyOld, hadj⟩

/-- Every extreme vertex of the canonical cap is either an old H-polyhedron
vertex, or a horizon vertex adjacent to one. -/
theorem cap_vertex_old_or_horizon_adjacent
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) (T : ℝ)
    (x : EuclideanSpace ℝ (Fin d))
    (hx : x ∈ extremePoints ℝ (cappedHpoly a b T)) :
    x ∈ extremePoints ℝ (Hpoly a b) ∨
      (⟪capNormal a, x⟫ = T ∧
        ∃ y, y ∈ extremePoints ℝ (Hpoly a b) ∧
          Adj (cappedHpoly a b T) y x) := by
  have hcaple : ⟪capNormal a, x⟫ ≤ T := hx.1.2
  rcases hcaple.eq_or_lt with heq | hlt
  · by_cases hold : x ∈ extremePoints ℝ (Hpoly a b)
    · exact Or.inl hold
    · exact Or.inr ⟨heq, new_horizon_adjacent_old_vertex a b T x hx heq hold⟩
  · left
    have hx' : x ∈ extremePoints ℝ
        (Hpoly a b ∩ {z | ⟪capNormal a, z⟫ ≤ T}) := by
      simpa [cappedHpoly] using hx
    exact HirschCut.strict_cut_extreme_to_parent
      (Hpoly a b) (hpoly_convex a b) (capNormal a) T hx' hlt


end HirschHpolyCap
end


-- BEGIN Solutions/PolynomialFaceReentrySplice.lean

open scoped RealInnerProductSpace
open Set Hirsch

set_option maxHeartbeats 4000000

noncomputable section

namespace HirschFaceSplice

/-- A parent extreme point lying in an extreme face is also extreme in that
face. -/
lemma extreme_in_extreme_face {d : ℕ}
    {P F : Set (EuclideanSpace ℝ (Fin d))}
    (hF : IsExtreme ℝ P F)
    {x : EuclideanSpace ℝ (Fin d)}
    (hx : x ∈ extremePoints ℝ P) (hxF : x ∈ F) :
    x ∈ extremePoints ℝ F := by
  refine ⟨hxF, ?_⟩
  intro p hp q hq hopen
  exact hx.2 (hF.1 hp) (hF.1 hq) hopen

/-- Every edge of an extreme face is an edge of the parent polytope. -/
lemma face_adj_to_parent {d : ℕ}
    {P F : Set (EuclideanSpace ℝ (Fin d))}
    (hF : IsExtreme ℝ P F)
    {x y : EuclideanSpace ℝ (Fin d)}
    (hxy : Adj F x y) : Adj P x y :=
  ⟨hxy.1, hF.trans hxy.2⟩

/-- Replace an arbitrary segment between two visits to an extreme face by a
shortest padded walk inside that face.

If a parent path of length `L` visits `F` at indices `s ≤ t`, and `F` has
face-diameter budget `B`, the repaired parent path has exact budget

` s + B + (L - t) `.

Crucially this depends only on the first/last selected visits, not on how many
times the original path left and re-entered `F` between them. -/
theorem splice_reentry_through_extreme_face
    (d L B s t : ℕ)
    (P F : Set (EuclideanSpace ℝ (Fin d)))
    (hF : IsExtreme ℝ P F)
    (hFD : DiamLE F B)
    (u v : EuclideanSpace ℝ (Fin d))
    (w : ℕ → EuclideanSpace ℝ (Fin d))
    (hw0 : w 0 = u) (hwL : w L = v)
    (hwstep : ∀ j < L, w j = w (j + 1) ∨ Adj P (w j) (w (j + 1)))
    (hst : s ≤ t) (htL : t ≤ L)
    (hsP : w s ∈ extremePoints ℝ P)
    (htP : w t ∈ extremePoints ℝ P)
    (hsF : w s ∈ F) (htF : w t ∈ F) :
    ∃ w' : ℕ → EuclideanSpace ℝ (Fin d),
      w' 0 = u ∧ w' (s + B + (L - t)) = v ∧
      ∀ j < s + B + (L - t),
        w' j = w' (j + 1) ∨ Adj P (w' j) (w' (j + 1)) := by
  have hsL : s ≤ L := hst.trans htL
  have hsFext : w s ∈ extremePoints ℝ F :=
    extreme_in_extreme_face hF hsP hsF
  have htFext : w t ∈ extremePoints ℝ F :=
    extreme_in_extreme_face hF htP htF

  obtain ⟨wf, hwf0, hwfB, hwfstep⟩ := hFD (w s) hsFext (w t) htFext
  have hwfstepP : ∀ j < B,
      wf j = wf (j + 1) ∨ Adj P (wf j) (wf (j + 1)) := by
    intro j hj
    rcases hwfstep j hj with heq | hadj
    · exact Or.inl heq
    · exact Or.inr (face_adj_to_parent hF hadj)

  let wp : ℕ → EuclideanSpace ℝ (Fin d) := fun j => w j
  have hwp0 : wp 0 = u := by simpa [wp] using hw0
  have hwps : wp s = w s := rfl
  have hwpstep : ∀ j < s,
      wp j = wp (j + 1) ∨ Adj P (wp j) (wp (j + 1)) := by
    intro j hj
    simpa [wp] using hwstep j (lt_of_lt_of_le hj hsL)

  let ws : ℕ → EuclideanSpace ℝ (Fin d) := fun j => w (t + j)
  have hws0 : ws 0 = w t := by simp [ws]
  have hwsB : ws (L - t) = v := by
    have hidx : t + (L - t) = L := by omega
    simpa [ws, hidx] using hwL
  have hwsstep : ∀ j < L - t,
      ws j = ws (j + 1) ∨ Adj P (ws j) (ws (j + 1)) := by
    intro j hj
    have hidx : t + j < L := by omega
    have h := hwstep (t + j) hidx
    simpa [ws, Nat.add_assoc] using h

  obtain ⟨wpf, hwpf0, hwpfB, hwpfstep⟩ :=
    HirschProduct.append_walk (Adj P) wp wf
      hwp0 hwps hwf0 hwfB hwpstep hwfstepP
  obtain ⟨w', hw'0, hw'B, hw'step⟩ :=
    HirschProduct.append_walk (Adj P) wpf ws
      hwpf0 hwpfB hws0 hwsB hwpfstep hwsstep
  refine ⟨w', hw'0, ?_, ?_⟩
  · simpa [Nat.add_assoc] using hw'B
  · simpa [Nat.add_assoc] using hw'step

/-- If the face diameter is no larger than the span of the segment being
replaced, re-entry can be eliminated without increasing the original path
budget. -/
theorem splice_reentry_no_growth
    (d L B s t : ℕ)
    (P F : Set (EuclideanSpace ℝ (Fin d)))
    (hF : IsExtreme ℝ P F)
    (hFD : DiamLE F B)
    (u v : EuclideanSpace ℝ (Fin d))
    (w : ℕ → EuclideanSpace ℝ (Fin d))
    (hw0 : w 0 = u) (hwL : w L = v)
    (hwstep : ∀ j < L, w j = w (j + 1) ∨ Adj P (w j) (w (j + 1)))
    (hst : s ≤ t) (htL : t ≤ L)
    (hsP : w s ∈ extremePoints ℝ P)
    (htP : w t ∈ extremePoints ℝ P)
    (hsF : w s ∈ F) (htF : w t ∈ F)
    (hB : B ≤ t - s) :
    ∃ w' : ℕ → EuclideanSpace ℝ (Fin d),
      w' 0 = u ∧ w' L = v ∧
      ∀ j < L, w' j = w' (j + 1) ∨ Adj P (w' j) (w' (j + 1)) := by
  obtain ⟨w0, h0, hK, hs⟩ :=
    splice_reentry_through_extreme_face
      d L B s t P F hF hFD u v w hw0 hwL hwstep
      hst htL hsP htP hsF htF
  have hKL : s + B + (L - t) ≤ L := by omega
  exact HirschProduct.pad_walk (Adj P) hKL w0 h0 hK hs

/-- Without any span comparison, all re-entry through one fixed face costs at
most one copy of that face's diameter budget. -/
theorem splice_reentry_cost_at_most_face_diameter
    (d L B s t : ℕ)
    (P F : Set (EuclideanSpace ℝ (Fin d)))
    (hF : IsExtreme ℝ P F)
    (hFD : DiamLE F B)
    (u v : EuclideanSpace ℝ (Fin d))
    (w : ℕ → EuclideanSpace ℝ (Fin d))
    (hw0 : w 0 = u) (hwL : w L = v)
    (hwstep : ∀ j < L, w j = w (j + 1) ∨ Adj P (w j) (w (j + 1)))
    (hst : s ≤ t) (htL : t ≤ L)
    (hsP : w s ∈ extremePoints ℝ P)
    (htP : w t ∈ extremePoints ℝ P)
    (hsF : w s ∈ F) (htF : w t ∈ F) :
    ∃ w' : ℕ → EuclideanSpace ℝ (Fin d),
      w' 0 = u ∧ w' (L + B) = v ∧
      ∀ j < L + B,
        w' j = w' (j + 1) ∨ Adj P (w' j) (w' (j + 1)) := by
  obtain ⟨w0, h0, hK, hs⟩ :=
    splice_reentry_through_extreme_face
      d L B s t P F hF hFD u v w hw0 hwL hwstep
      hst htL hsP htP hsF htF
  have hKL : s + B + (L - t) ≤ L + B := by omega
  exact HirschProduct.pad_walk (Adj P) hKL w0 h0 hK hs


end HirschFaceSplice
end


-- BEGIN Solutions/PolynomialRegionRouting.lean

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

noncomputable section

namespace HirschRegionRoute

/-- A padded route using only the supplied relation. -/
def Route {V : Type*} (R : V → V → Prop) (B : ℕ) (u v : V) : Prop :=
  ∃ w : ℕ → V, w 0 = u ∧ w B = v ∧
    ∀ j < B, w j = w (j + 1) ∨ R (w j) (w (j + 1))

/-- Region intersections, not overlap of intervals in an old sequence. -/
def intersectionGraph {V ι : Type*} (S : ι → Set V) : SimpleGraph ι where
  Adj i j := i ≠ j ∧ ∃ z, z ∈ S i ∧ z ∈ S j
  symm := by
    intro i j h
    obtain ⟨hne, z, hi, hj⟩ := h
    exact ⟨hne.symm, z, hj, hi⟩
  loopless := ⟨fun i h => h.1 rfl⟩

lemma shared_point_walk {V ι : Type*} (S : ι → Set V)
    {i j : ι} {z : V} (hi : z ∈ S i) (hj : z ∈ S j) :
    Nonempty ((intersectionGraph S).Walk i j) := by
  classical
  by_cases hij : i = j
  · subst j
    exact ⟨.nil⟩
  · exact ⟨.cons ⟨hij, z, hi, hj⟩ .nil⟩

/-- Traverse a walk of regions, paying the cost of each region occurrence. -/
theorem route_of_region_walk {V ι : Type*}
    (R : V → V → Prop) (S : ι → Set V) (C : ι → ℕ)
    (hlocal : ∀ i, ∀ u ∈ S i, ∀ v ∈ S i, Route R (C i) u v)
    {i j : ι} (p : (intersectionGraph S).Walk i j) :
    ∀ u ∈ S i, ∀ v ∈ S j, Route R ((p.support.map C).sum) u v := by
  induction p with
  | @nil i =>
      intro u hu v hv
      simpa using hlocal i u hu v hv
  | @cons i k j hik p ih =>
      intro u hu v hv
      obtain ⟨z, hzi, hzk⟩ := hik.2
      obtain ⟨a, ha0, haC, has⟩ := hlocal i u hu z hzi
      obtain ⟨b, hb0, hbC, hbs⟩ := ih z hzk v hv
      obtain ⟨q, hq0, hqC, hqs⟩ :=
        HirschProduct.append_walk R a b ha0 haC hb0 hbC has hbs
      exact ⟨q, hq0, hqC, hqs⟩

/-- A list without repeated labels charges each available region at most once. -/
lemma nodup_cost_le {ι : Type*} (C : ι → ℕ) (l : List ι)
    (s : Finset ι) (hnd : l.Nodup) (hsub : ∀ i ∈ l, i ∈ s) :
    (l.map C).sum ≤ ∑ i ∈ s, C i := by
  classical
  induction l generalizing s with
  | nil => simp
  | cons a l ih =>
      have hp := List.nodup_cons.mp hnd
      have ha : a ∈ s := hsub a (by simp)
      have htail : ∀ i ∈ l, i ∈ s.erase a := by
        intro i hi
        apply Finset.mem_erase.mpr
        refine ⟨?_, hsub i (by simp [hi])⟩
        intro hia
        subst i
        exact hp.1 hi
      have ht := ih (s.erase a) hp.2 htail
      have heq := Finset.add_sum_erase s C ha
      simpa only [List.map_cons, List.sum_cons] using
        (Nat.add_le_add_left ht (C a)).trans_eq heq

/-- Erasing repeated region labels gives a one-charge-per-region bound.
No order or laminarity assumption is made about appearances in an old walk. -/
theorem route_of_connected_regions {V ι : Type*} [Fintype ι]
    (R : V → V → Prop) (S : ι → Set V) (C : ι → ℕ)
    (hlocal : ∀ i, ∀ u ∈ S i, ∀ v ∈ S i, Route R (C i) u v)
    {i j : ι} (hreach : Nonempty ((intersectionGraph S).Walk i j))
    (u v : V) (hu : u ∈ S i) (hv : v ∈ S j) :
    Route R (∑ k, C k) u v := by
  classical
  obtain ⟨walk⟩ := hreach
  let p := walk.toPath
  have hnd : p.val.support.Nodup := p.property.support_nodup
  have hle := nodup_cost_le C p.val.support Finset.univ hnd (by simp)
  obtain ⟨q, hq0, hqB, hqstep⟩ := route_of_region_walk R S C hlocal p.val u hu v hv
  exact HirschProduct.pad_walk R hle q hq0 hqB hqstep

/-- If every consecutive pair is covered by a region, endpoint region labels
are connected even when regions are revisited in an arbitrary order. -/
lemma region_walk_of_step_cover {V ι : Type*}
    (S : ι → Set V) (w : ℕ → V) (L : ℕ)
    (hcover : ∀ k < L, ∃ i, w k ∈ S i ∧ w (k + 1) ∈ S i)
    (i j : ι) (hi : w 0 ∈ S i) (hj : w L ∈ S j) :
    Nonempty ((intersectionGraph S).Walk i j) := by
  induction L generalizing j with
  | zero => exact shared_point_walk S hi hj
  | succ L ih =>
      obtain ⟨k, hkL, hkNext⟩ := hcover L (Nat.lt_succ_self L)
      obtain ⟨p⟩ := ih (fun a ha => hcover a (Nat.lt_succ_of_lt ha)) k hkL
      obtain ⟨q⟩ := shared_point_walk S hkNext hj
      exact ⟨p.append q⟩

/-- Compress arbitrarily many covered transitions into a route whose budget
is the sum over distinct available regions, not the sum over occurrences. -/
theorem route_of_step_cover {V ι : Type*} [Fintype ι]
    (R : V → V → Prop) (S : ι → Set V) (C : ι → ℕ)
    (hlocal : ∀ i, ∀ u ∈ S i, ∀ v ∈ S i, Route R (C i) u v)
    (w : ℕ → V) (L : ℕ)
    (hcover : ∀ k < L, ∃ i, w k ∈ S i ∧ w (k + 1) ∈ S i) :
    Route R (∑ i, C i) (w 0) (w L) := by
  by_cases hL : L = 0
  · subst L
    exact ⟨fun _ => w 0, rfl, rfl, fun _ _ => Or.inl rfl⟩
  · have hpos : 0 < L := Nat.pos_of_ne_zero hL
    obtain ⟨i, hi, _⟩ := hcover 0 hpos
    obtain ⟨j, _, hj⟩ := hcover (L - 1) (by omega)
    have hj' : w L ∈ S j := by simpa [Nat.sub_add_cancel (by omega : 1 ≤ L)] using hj
    exact route_of_connected_regions R S C hlocal
      (region_walk_of_step_cover S w L hcover i j hi hj') (w 0) (w L) hi hj'

/-- An extreme face supplies a routing region on the parent's extreme vertices. -/
lemma extreme_face_region {d : ℕ}
    (P F : Set (EuclideanSpace ℝ (Fin d))) (B : ℕ)
    (hF : IsExtreme ℝ P F) (hD : DiamLE F B) :
    ∀ u ∈ extremePoints ℝ P ∩ F, ∀ v ∈ extremePoints ℝ P ∩ F,
      Route (Adj P) B u v := by
  intro u hu v hv
  obtain ⟨q, hq0, hqB, hs⟩ := hD u
    (HirschFaceSplice.extreme_in_extreme_face hF hu.1 hu.2) v
    (HirschFaceSplice.extreme_in_extreme_face hF hv.1 hv.2)
  refine ⟨q, hq0, hqB, ?_⟩
  intro k hk
  rcases hs k hk with heq | hadj
  · exact Or.inl heq
  · exact Or.inr (HirschFaceSplice.face_adj_to_parent hF hadj)

/-- Face-covered transitions can be arbitrarily interleaved. Repeated visits
to the same face do not multiply its cost, provided every transition is
certified by an actual common face of its two parent vertices. -/
theorem route_of_face_covered_sequence {d : ℕ} {ι : Type*} [Fintype ι]
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (F : ι → Set (EuclideanSpace ℝ (Fin d))) (B : ι → ℕ)
    (hF : ∀ i, IsExtreme ℝ P (F i)) (hD : ∀ i, DiamLE (F i) (B i))
    (w : ℕ → EuclideanSpace ℝ (Fin d)) (L : ℕ)
    (hverts : ∀ k ≤ L, w k ∈ extremePoints ℝ P)
    (hcover : ∀ k < L, ∃ i, w k ∈ F i ∧ w (k + 1) ∈ F i) :
    Route (Adj P) (∑ i, B i) (w 0) (w L) := by
  apply route_of_step_cover (Adj P) (fun i => extremePoints ℝ P ∩ F i) B
    (fun i => extreme_face_region P (F i) (B i) (hF i) (hD i)) w L
  intro k hk
  obtain ⟨i, hi, hi'⟩ := hcover k hk
  exact ⟨i, ⟨hverts k (by omega), hi⟩, ⟨hverts (k + 1) (by omega), hi'⟩⟩


end HirschRegionRoute
end


-- BEGIN Solutions/PolynomialMixedRegionRouting.lean

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

noncomputable section

namespace HirschRegionRoute

lemma route_one {V : Type*} (R : V → V → Prop) {u v : V}
    (h : u = v ∨ R u v) : Route R 1 u v := by
  refine ⟨fun k => if k = 0 then u else v, by simp, by simp, ?_⟩
  intro k hk
  have hk0 : k = 0 := by omega
  subst k
  simpa using h

lemma pair_region {V : Type*} (R : V → V → Prop) (a b : V)
    (hab : R a b) (hba : R b a) :
    ∀ u ∈ ({a, b} : Set V), ∀ v ∈ ({a, b} : Set V), Route R 1 u v := by
  intro u hu v hv
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
  · exact route_one R (Or.inl rfl)
  · exact route_one R (Or.inr hab)
  · exact route_one R (Or.inr hba)
  · exact route_one R (Or.inl rfl)

/-- Repeated uses of the same repair region or surviving bridge do not
multiply its charge. Chronological crossing of region visits is allowed. -/
theorem route_of_mixed_step_cover {V ι κ : Type*} [Fintype ι] [Fintype κ]
    (R : V → V → Prop) (S : ι → Set V) (C : ι → ℕ)
    (hlocal : ∀ i, ∀ u ∈ S i, ∀ v ∈ S i, Route R (C i) u v)
    (a b : κ → V) (hab : ∀ k, R (a k) (b k)) (hba : ∀ k, R (b k) (a k))
    (w : ℕ → V) (L : ℕ)
    (hcover : ∀ k < L,
      (∃ i, w k ∈ S i ∧ w (k + 1) ∈ S i) ∨
      (∃ e, w k ∈ ({a e, b e} : Set V) ∧ w (k + 1) ∈ ({a e, b e} : Set V))) :
    Route R ((∑ i, C i) + Fintype.card κ) (w 0) (w L) := by
  let T : Sum ι κ → Set V := Sum.elim S (fun e => {a e, b e})
  let D : Sum ι κ → ℕ := Sum.elim C (fun _ => 1)
  have hlocalT : ∀ i, ∀ u ∈ T i, ∀ v ∈ T i, Route R (D i) u v := by
    intro i
    cases i with
    | inl i => exact hlocal i
    | inr e => exact pair_region R (a e) (b e) (hab e) (hba e)
  have hcoverT : ∀ k < L, ∃ i, w k ∈ T i ∧ w (k + 1) ∈ T i := by
    intro k hk
    rcases hcover k hk with ⟨i, hi, hi'⟩ | ⟨e, he, he'⟩
    · exact ⟨Sum.inl i, hi, hi'⟩
    · exact ⟨Sum.inr e, he, he'⟩
  have h := route_of_step_cover R T D hlocalT w L hcoverT
  simpa [D, Fintype.sum_sum_type] using h

/-- Unordered face-damage amortization in the parent vertex graph.
The input need not be a valid graph walk. Each consecutive pair must instead
lie in one certified extreme face or on one listed surviving edge. The output
pays each available face once plus one for each listed surviving edge. -/
theorem route_of_faces_and_surviving_edges
    {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (F : ι → Set (EuclideanSpace ℝ (Fin d))) (B : ι → ℕ)
    (hF : ∀ i, IsExtreme ℝ P (F i)) (hD : ∀ i, DiamLE (F i) (B i))
    (a b : κ → EuclideanSpace ℝ (Fin d)) (hedge : ∀ e, Adj P (a e) (b e))
    (w : ℕ → EuclideanSpace ℝ (Fin d)) (L : ℕ)
    (hverts : ∀ k ≤ L, w k ∈ extremePoints ℝ P)
    (hcover : ∀ k < L,
      (∃ i, w k ∈ F i ∧ w (k + 1) ∈ F i) ∨
      (∃ e, w k ∈ ({a e, b e} : Set (EuclideanSpace ℝ (Fin d))) ∧
        w (k + 1) ∈ ({a e, b e} : Set (EuclideanSpace ℝ (Fin d))))) :
    Route (Adj P) ((∑ i, B i) + Fintype.card κ) (w 0) (w L) := by
  have hrev : ∀ e, Adj P (b e) (a e) := by
    intro e
    refine ⟨(hedge e).1.symm, ?_⟩
    rw [segment_symm]
    exact (hedge e).2
  apply route_of_mixed_step_cover (Adj P) (fun i => extremePoints ℝ P ∩ F i) B
    (fun i => extreme_face_region P (F i) (B i) (hF i) (hD i)) a b hedge hrev w L
  intro k hk
  rcases hcover k hk with ⟨i, hi, hi'⟩ | hgood
  · exact Or.inl ⟨i, ⟨hverts k (by omega), hi⟩,
      ⟨hverts (k + 1) (by omega), hi'⟩⟩
  · exact Or.inr hgood


end HirschRegionRoute
end


-- BEGIN Solutions/PolynomialIntervalRegionRouting.lean

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

noncomputable section

namespace HirschRegionRoute

/-- A chronological interval cover connects its endpoint regions when every
closed interval overlap is backed by an actual shared point of the regions.
Interior entries of the old sequence are not used as portals. -/
lemma region_walk_of_interval_cover {V ι : Type*}
    (S : ι → Set V) (s t : ι → ℕ)
    (hportal : ∀ i j, s i ≤ t j → s j ≤ t i →
      ∃ z, z ∈ S i ∧ z ∈ S j)
    (L : ℕ)
    (hcover : ∀ k < L, ∃ i, s i ≤ k ∧ k + 1 ≤ t i)
    (i j : ι) (hi : s i ≤ 0 ∧ 0 ≤ t i)
    (hj : s j ≤ L ∧ L ≤ t j) :
    Nonempty ((intersectionGraph S).Walk i j) := by
  induction L generalizing j with
  | zero =>
      obtain ⟨z, hzi, hzj⟩ := hportal i j
        (hi.1.trans hj.2) (hj.1.trans hi.2)
      exact shared_point_walk S hzi hzj
  | succ L ih =>
      obtain ⟨k, hks, hkt⟩ := hcover L (Nat.lt_succ_self L)
      obtain ⟨p⟩ := ih (fun a ha => hcover a (Nat.lt_succ_of_lt ha)) k
        ⟨hks, (Nat.le_succ L).trans hkt⟩
      obtain ⟨z, hzk, hzj⟩ := hportal k j
        (hks.trans ((Nat.le_succ L).trans hj.2)) (hj.1.trans hkt)
      obtain ⟨q⟩ := shared_point_walk S hzk hzj
      exact ⟨p.append q⟩

/-- Unordered endpoint-supported interval repair. The sequence may have invalid
steps and arbitrary interior points. It is enough that intervals cover every
step, each interval's endpoints lie in its routing region, and chronological
overlaps have genuine region portals. Every available region is charged once.

This does not infer geometric intersection from temporal overlap: `hportal`
is the separate geometric hypothesis which makes crossing intervals safe. -/
theorem route_of_interval_cover {V ι : Type*} [Fintype ι]
    (R : V → V → Prop) (S : ι → Set V) (C : ι → ℕ)
    (hlocal : ∀ i, ∀ u ∈ S i, ∀ v ∈ S i, Route R (C i) u v)
    (s t : ι → ℕ) (w : ℕ → V) (L : ℕ)
    (hbound : ∀ i, t i ≤ L)
    (hends : ∀ i, w (s i) ∈ S i ∧ w (t i) ∈ S i)
    (hcover : ∀ k < L, ∃ i, s i ≤ k ∧ k + 1 ≤ t i)
    (hportal : ∀ i j, s i ≤ t j → s j ≤ t i →
      ∃ z, z ∈ S i ∧ z ∈ S j) :
    Route R (∑ i, C i) (w 0) (w L) := by
  by_cases hL : L = 0
  · subst L
    exact ⟨fun _ => w 0, rfl, rfl, fun _ _ => Or.inl rfl⟩
  · have hpos : 0 < L := Nat.pos_of_ne_zero hL
    obtain ⟨i, hsi, hti⟩ := hcover 0 hpos
    have hsi0 : s i = 0 := Nat.eq_zero_of_le_zero hsi
    obtain ⟨j, hsj, htj⟩ := hcover (L - 1) (by omega)
    have hlast : L - 1 + 1 = L := Nat.sub_add_cancel (by omega : 1 ≤ L)
    rw [hlast] at htj
    have htjL : t j = L := Nat.le_antisymm (hbound j) htj
    have hi : w 0 ∈ S i := by simpa only [hsi0] using (hends i).1
    have hj : w L ∈ S j := by simpa only [htjL] using (hends j).2
    have hreach := region_walk_of_interval_cover S s t hportal L hcover i j
      ⟨hsi, Nat.zero_le _⟩ ⟨hsj.trans (Nat.sub_le _ _), htj⟩
    exact route_of_connected_regions R S C hlocal hreach (w 0) (w L) hi hj

/-- Geometric specialization: a shared parent extreme vertex is a valid portal
between two extreme-face repairs. Only marked interval endpoints must remain
parent vertices; the old sequence's interior entries need not remain feasible.
The conclusion is conditional on the stated portal and face-diameter data. -/
theorem route_of_face_interval_cover {d : ℕ} {ι : Type*} [Fintype ι]
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (F : ι → Set (EuclideanSpace ℝ (Fin d))) (B : ι → ℕ)
    (hF : ∀ i, IsExtreme ℝ P (F i)) (hD : ∀ i, DiamLE (F i) (B i))
    (s t : ι → ℕ) (w : ℕ → EuclideanSpace ℝ (Fin d)) (L : ℕ)
    (hbound : ∀ i, t i ≤ L)
    (hverts : ∀ i, w (s i) ∈ extremePoints ℝ P ∧ w (t i) ∈ extremePoints ℝ P)
    (hends : ∀ i, w (s i) ∈ F i ∧ w (t i) ∈ F i)
    (hcover : ∀ k < L, ∃ i, s i ≤ k ∧ k + 1 ≤ t i)
    (hportal : ∀ i j, s i ≤ t j → s j ≤ t i →
      ∃ z, z ∈ extremePoints ℝ P ∧ z ∈ F i ∧ z ∈ F j) :
    Route (Adj P) (∑ i, B i) (w 0) (w L) := by
  apply route_of_interval_cover (Adj P) (fun i => extremePoints ℝ P ∩ F i) B
    (fun i => extreme_face_region P (F i) (B i) (hF i) (hD i)) s t w L hbound
  · intro i
    exact ⟨⟨(hverts i).1, (hends i).1⟩, ⟨(hverts i).2, (hends i).2⟩⟩
  · exact hcover
  · intro i j hij hji
    obtain ⟨z, hz, hzi, hzj⟩ := hportal i j hij hji
    exact ⟨z, ⟨hz, hzi⟩, ⟨hz, hzj⟩⟩


end HirschRegionRoute
end


-- BEGIN Solutions/PolynomialIntervalStartPortals.lean

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

noncomputable section

namespace HirschRegionRoute

/-- Chronological overlap has an automatic region portal when every interval
contains the start point of every later interval that begins before it ends.
The later start itself is the shared point. -/
lemma interval_portal_of_start_containment {V ι : Type*}
    (S : ι → Set V) (s t : ι → ℕ) (w : ℕ → V)
    (hstart : ∀ j, w (s j) ∈ S j)
    (hcontain : ∀ i j, s i ≤ s j → s j ≤ t i → w (s j) ∈ S i) :
    ∀ i j, s i ≤ t j → s j ≤ t i →
      ∃ z, z ∈ S i ∧ z ∈ S j := by
  intro i j hij hji
  by_cases hs : s i ≤ s j
  · exact ⟨w (s j), hcontain i j hs hji, hstart j⟩
  · have hjs : s j ≤ s i := Nat.le_of_not_ge hs
    exact ⟨w (s i), hstart i, hcontain j i hjs hij⟩

/-- Generic interval routing with no separate existential portal hypothesis:
start-containment implies the portal condition required by `route_of_interval_cover`. -/
theorem route_of_interval_cover_of_start_containment
    {V ι : Type*} [Fintype ι]
    (R : V → V → Prop) (S : ι → Set V) (C : ι → ℕ)
    (hlocal : ∀ i, ∀ u ∈ S i, ∀ v ∈ S i, Route R (C i) u v)
    (s t : ι → ℕ) (w : ℕ → V) (L : ℕ)
    (hbound : ∀ i, t i ≤ L)
    (hends : ∀ i, w (s i) ∈ S i ∧ w (t i) ∈ S i)
    (hcover : ∀ k < L, ∃ i, s i ≤ k ∧ k + 1 ≤ t i)
    (hcontain : ∀ i j, s i ≤ s j → s j ≤ t i → w (s j) ∈ S i) :
    Route R (∑ i, C i) (w 0) (w L) := by
  apply route_of_interval_cover R S C hlocal s t w L hbound hends hcover
  exact interval_portal_of_start_containment S s t w (fun j => (hends j).1) hcontain

/-- Extreme-face specialization.  It is enough that each interval's start and
end are parent vertices in its own face, and that a later interval start which
occurs before an earlier interval ends lies in the earlier supporting face.
The later start is then a genuine parent-vertex portal between the two faces. -/
theorem route_of_face_interval_cover_of_start_containment
    {d : ℕ} {ι : Type*} [Fintype ι]
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (F : ι → Set (EuclideanSpace ℝ (Fin d))) (B : ι → ℕ)
    (hF : ∀ i, IsExtreme ℝ P (F i)) (hD : ∀ i, DiamLE (F i) (B i))
    (s t : ι → ℕ) (w : ℕ → EuclideanSpace ℝ (Fin d)) (L : ℕ)
    (hbound : ∀ i, t i ≤ L)
    (hverts : ∀ i, w (s i) ∈ extremePoints ℝ P ∧ w (t i) ∈ extremePoints ℝ P)
    (hends : ∀ i, w (s i) ∈ F i ∧ w (t i) ∈ F i)
    (hcover : ∀ k < L, ∃ i, s i ≤ k ∧ k + 1 ≤ t i)
    (hcontain : ∀ i j, s i ≤ s j → s j ≤ t i → w (s j) ∈ F i) :
    Route (Adj P) (∑ i, B i) (w 0) (w L) := by
  apply route_of_face_interval_cover P F B hF hD s t w L hbound hverts hends hcover
  intro i j hij hji
  by_cases hs : s i ≤ s j
  · exact ⟨w (s j), (hverts j).1, hcontain i j hs hji, (hends j).1⟩
  · have hjs : s j ≤ s i := Nat.le_of_not_ge hs
    exact ⟨w (s i), (hverts i).1, (hends i).1, hcontain j i hjs hij⟩

/-- More geometric but stronger sufficient hypothesis: if every checkpoint of
an interval remains in its supporting face throughout that valid interval,
then start-containment is automatic and the same total face-budget route
follows. This is the form closest to a Case-VII statement that a damaged path
segment lies in one common face. -/
theorem route_of_face_interval_cover_of_active_containment
    {d : ℕ} {ι : Type*} [Fintype ι]
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (F : ι → Set (EuclideanSpace ℝ (Fin d))) (B : ι → ℕ)
    (hF : ∀ i, IsExtreme ℝ P (F i)) (hD : ∀ i, DiamLE (F i) (B i))
    (s t : ι → ℕ) (w : ℕ → EuclideanSpace ℝ (Fin d)) (L : ℕ)
    (hvalid : ∀ i, s i ≤ t i)
    (hbound : ∀ i, t i ≤ L)
    (hverts : ∀ i, w (s i) ∈ extremePoints ℝ P ∧ w (t i) ∈ extremePoints ℝ P)
    (hcover : ∀ k < L, ∃ i, s i ≤ k ∧ k + 1 ≤ t i)
    (hactive : ∀ i k, s i ≤ k → k ≤ t i → w k ∈ F i) :
    Route (Adj P) (∑ i, B i) (w 0) (w L) := by
  apply route_of_face_interval_cover_of_start_containment
    P F B hF hD s t w L hbound hverts
    (fun i => ⟨hactive i (s i) (Nat.le_refl _) (hvalid i),
      hactive i (t i) (hvalid i) (Nat.le_refl _)⟩)
    hcover
  intro i j hs hst
  exact hactive i (s j) hs hst


end HirschRegionRoute
end


-- BEGIN Solutions/PolynomialFacePreservingCheckpoints.lean

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

noncomputable section

namespace HirschRegionRoute

/-- A nonempty closed extreme subset of a compact parent contains a parent
extreme vertex. The given point need not itself be a vertex. -/
theorem compact_face_point_has_parent_vertex
    {d : ℕ} (P F : Set (EuclideanSpace ℝ (Fin d)))
    (hP : IsCompact P) (hF : IsExtreme ℝ P F) (hclosed : IsClosed F)
    (hne : F.Nonempty) :
    ∃ v, v ∈ extremePoints ℝ P ∧ v ∈ F := by
  obtain ⟨v, hv⟩ :=
    (hP.of_isClosed_subset hclosed hF.subset).extremePoints_nonempty hne
  exact ⟨v, hF.extremePoints_subset_extremePoints hv, hv.1⟩

/-- All closed parent extreme faces containing a feasible point can be
preserved simultaneously by one parent vertex. No finiteness assumption on
the face family is necessary. This is an incidence selector, not a continuous
map, a nearest-vertex map, or a claim that a circuit step is an edge. -/
theorem exists_vertex_preserving_face_memberships
    {d : ℕ} {ι : Type*} (P : Set (EuclideanSpace ℝ (Fin d)))
    (F : ι → Set (EuclideanSpace ℝ (Fin d)))
    (hP : IsCompact P) (hF : ∀ i, IsExtreme ℝ P (F i))
    (hclosed : ∀ i, IsClosed (F i))
    (x : EuclideanSpace ℝ (Fin d)) (hx : x ∈ P) :
    ∃ v, v ∈ extremePoints ℝ P ∧ ∀ i, x ∈ F i → v ∈ F i := by
  let G : Set (EuclideanSpace ℝ (Fin d)) :=
    P ∩ ⋂ i, ⋂ (_ : x ∈ F i), F i
  have hGc : IsClosed G :=
    hP.isClosed.inter (isClosed_iInter fun i => isClosed_iInter fun _ => hclosed i)
  have hxG : x ∈ G :=
    ⟨hx, mem_iInter.mpr fun i => mem_iInter.mpr fun hi => hi⟩
  have hGe : IsExtreme ℝ P G := by
    refine ⟨fun _ hz => hz.1, ?_⟩
    intro a ha b hb z hz hseg
    refine ⟨ha, mem_iInter.mpr fun i => mem_iInter.mpr fun hi => ?_⟩
    exact (hF i).left_mem_of_mem_openSegment ha hb
      (mem_iInter.mp (mem_iInter.mp hz.2 i) hi) hseg
  obtain ⟨v, hv, hvG⟩ := compact_face_point_has_parent_vertex P G hP hGe hGc ⟨x, hxG⟩
  exact ⟨v, hv, fun i hi => mem_iInter.mp (mem_iInter.mp hvG.2 i) hi⟩

/-- A single face-membership-preserving vertex selection fixes every parent
vertex. It may be discontinuous and need not preserve adjacency. -/
theorem face_preserving_vertex_selection
    {d : ℕ} {ι : Type*} (P : Set (EuclideanSpace ℝ (Fin d)))
    (F : ι → Set (EuclideanSpace ℝ (Fin d)))
    (hP : IsCompact P) (hF : ∀ i, IsExtreme ℝ P (F i))
    (hclosed : ∀ i, IsClosed (F i)) :
    ∃ r : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d),
      (∀ x ∈ P, r x ∈ extremePoints ℝ P) ∧
      (∀ x ∈ extremePoints ℝ P, r x = x) ∧
      (∀ i x, x ∈ F i → r x ∈ F i) := by
  classical
  have hchoice : ∀ x : EuclideanSpace ℝ (Fin d), ∃ v,
      (x ∈ P → v ∈ extremePoints ℝ P) ∧
      (x ∈ extremePoints ℝ P → v = x) ∧
      (∀ i, x ∈ F i → v ∈ F i) := by
    intro x
    by_cases hxv : x ∈ extremePoints ℝ P
    · exact ⟨x, fun _ => hxv, fun _ => rfl, fun _ hi => hi⟩
    · by_cases hx : x ∈ P
      · obtain ⟨v, hv, hmem⟩ :=
          exists_vertex_preserving_face_memberships P F hP hF hclosed x hx
        exact ⟨v, fun _ => hv, fun h => False.elim (hxv h), hmem⟩
      · exact ⟨x, fun h => False.elim (hx h), fun _ => rfl, fun _ hi => hi⟩
  choose r hr using hchoice
  exact ⟨r, fun x hx => (hr x).1 hx, fun x hx => (hr x).2.1 hx,
    fun i x hx => (hr x).2.2 i hx⟩

/-- Geometric overlap of closed faces of a compact parent supplies a genuine
parent-vertex portal, even when the overlap witness is nonvertex. -/
theorem compact_faces_shared_point_portal
    {d : ℕ} (P F G : Set (EuclideanSpace ℝ (Fin d)))
    (hP : IsCompact P) (hF : IsExtreme ℝ P F) (hG : IsExtreme ℝ P G)
    (hFc : IsClosed F) (hGc : IsClosed G)
    (x : EuclideanSpace ℝ (Fin d)) (hxF : x ∈ F) (hxG : x ∈ G) :
    ∃ v, v ∈ extremePoints ℝ P ∧ v ∈ F ∧ v ∈ G := by
  obtain ⟨v, hv, hvFG⟩ := compact_face_point_has_parent_vertex
    P (F ∩ G) hP (hF.inter hG) (hFc.inter hGc) ⟨x, hxF, hxG⟩
  exact ⟨v, hv, hvFG.1, hvFG.2⟩

/-- A fixed feasible face-covered sequence needs vertex endpoints only.
Interior checkpoints are rounded simultaneously, preserving every available
face incidence and charging each face once. The actual face budgets remain
explicit hypotheses. -/
theorem route_of_feasible_face_covered_sequence
    {d : ℕ} {ι : Type*} [Fintype ι]
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (F : ι → Set (EuclideanSpace ℝ (Fin d))) (B : ι → ℕ)
    (hP : IsCompact P) (hF : ∀ i, IsExtreme ℝ P (F i))
    (hclosed : ∀ i, IsClosed (F i)) (hD : ∀ i, DiamLE (F i) (B i))
    (w : ℕ → EuclideanSpace ℝ (Fin d)) (L : ℕ)
    (hfeas : ∀ k ≤ L, w k ∈ P)
    (h0 : w 0 ∈ extremePoints ℝ P) (hL : w L ∈ extremePoints ℝ P)
    (hcover : ∀ k < L, ∃ i, w k ∈ F i ∧ w (k + 1) ∈ F i) :
    Route (Adj P) (∑ i, B i) (w 0) (w L) := by
  obtain ⟨r, hrP, hrfix, hrF⟩ := face_preserving_vertex_selection P F hP hF hclosed
  have hroute := route_of_face_covered_sequence P F B hF hD (fun k => r (w k)) L
    (fun k hk => hrP (w k) (hfeas k hk)) (by
      intro k hk
      obtain ⟨i, hi, hi'⟩ := hcover k hk
      exact ⟨i, hrF i (w k) hi, hrF i (w (k + 1)) hi'⟩)
  simpa only [hrfix (w 0) h0, hrfix (w L) hL] using hroute

/-- PR #48 start containment with feasible, possibly nonvertex marked
checkpoints. Membership in the closed parent faces supplies feasibility.
Only the two route endpoints must already be parent vertices. Unmarked
interiors of the old sequence need not be feasible. -/
theorem route_of_face_interval_cover_of_feasible_start_containment
    {d : ℕ} {ι : Type*} [Fintype ι]
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (F : ι → Set (EuclideanSpace ℝ (Fin d))) (B : ι → ℕ)
    (hP : IsCompact P) (hF : ∀ i, IsExtreme ℝ P (F i))
    (hclosed : ∀ i, IsClosed (F i)) (hD : ∀ i, DiamLE (F i) (B i))
    (s t : ι → ℕ) (w : ℕ → EuclideanSpace ℝ (Fin d)) (L : ℕ)
    (hbound : ∀ i, t i ≤ L)
    (h0 : w 0 ∈ extremePoints ℝ P) (hL : w L ∈ extremePoints ℝ P)
    (hends : ∀ i, w (s i) ∈ F i ∧ w (t i) ∈ F i)
    (hcover : ∀ k < L, ∃ i, s i ≤ k ∧ k + 1 ≤ t i)
    (hcontain : ∀ i j, s i ≤ s j → s j ≤ t i → w (s j) ∈ F i) :
    Route (Adj P) (∑ i, B i) (w 0) (w L) := by
  obtain ⟨r, hrP, hrfix, hrF⟩ := face_preserving_vertex_selection P F hP hF hclosed
  have hroute := route_of_face_interval_cover_of_start_containment
    P F B hF hD s t (fun k => r (w k)) L hbound
    (fun i => ⟨hrP (w (s i)) ((hF i).subset (hends i).1),
      hrP (w (t i)) ((hF i).subset (hends i).2)⟩)
    (fun i => ⟨hrF i (w (s i)) (hends i).1, hrF i (w (t i)) (hends i).2⟩)
    hcover (fun i j hs ht => hrF i (w (s j)) (hcontain i j hs ht))
  simpa only [hrfix (w 0) h0, hrfix (w L) hL] using hroute

/-- The active-containment corollary likewise needs no intermediate vertex
hypothesis. This does not assert that an evolving polytope's faces have
nonempty intersections in the fixed parent, or that their costs are small. -/
theorem route_of_face_interval_cover_of_feasible_active_containment
    {d : ℕ} {ι : Type*} [Fintype ι]
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (F : ι → Set (EuclideanSpace ℝ (Fin d))) (B : ι → ℕ)
    (hP : IsCompact P) (hF : ∀ i, IsExtreme ℝ P (F i))
    (hclosed : ∀ i, IsClosed (F i)) (hD : ∀ i, DiamLE (F i) (B i))
    (s t : ι → ℕ) (w : ℕ → EuclideanSpace ℝ (Fin d)) (L : ℕ)
    (hvalid : ∀ i, s i ≤ t i) (hbound : ∀ i, t i ≤ L)
    (h0 : w 0 ∈ extremePoints ℝ P) (hL : w L ∈ extremePoints ℝ P)
    (hcover : ∀ k < L, ∃ i, s i ≤ k ∧ k + 1 ≤ t i)
    (hactive : ∀ i k, s i ≤ k → k ≤ t i → w k ∈ F i) :
    Route (Adj P) (∑ i, B i) (w 0) (w L) := by
  apply route_of_face_interval_cover_of_feasible_start_containment
    P F B hP hF hclosed hD s t w L hbound h0 hL
    (fun i => ⟨hactive i (s i) (Nat.le_refl _) (hvalid i),
      hactive i (t i) (hvalid i) (Nat.le_refl _)⟩) hcover
  intro i j hs ht
  exact hactive i (s j) hs ht


end HirschRegionRoute
end


-- BEGIN Solutions/PolynomialRadialClipCells.lean

open Set

noncomputable section

namespace HirschRadial

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Retraction toward one fixed feasible centre. The scale will be the maximum
of 1 and the normalized final-cut violations, never a stage-dependent scale. -/
def point (o x : E) (μ : ℝ) : E := o + μ⁻¹ • (x - o)

lemma eval_point (f : E →ₗ[ℝ] ℝ) (o x : E) (μ : ℝ) :
    f (point o x μ) = f o + μ⁻¹ * (f x - f o) := by
  simp [point]

lemma point_mem_convex (Q : Set E) (hQ : Convex ℝ Q)
    {o x : E} (ho : o ∈ Q) (hx : x ∈ Q) {μ : ℝ} (hμ : 1 ≤ μ) :
    point o x μ ∈ Q := by
  have hpos : 0 < μ := lt_of_lt_of_le zero_lt_one hμ
  have hi : 0 ≤ μ⁻¹ := inv_nonneg.mpr hpos.le
  have hiμ : μ⁻¹ * μ = 1 := inv_mul_cancel₀ hpos.ne'
  have hi1 : μ⁻¹ ≤ 1 := by
    nlinarith [mul_nonneg hi (sub_nonneg.mpr hμ)]
  have h := hQ ho hx (sub_nonneg.mpr hi1) hi (by ring : (1 - μ⁻¹) + μ⁻¹ = 1)
  have heq : (1 - μ⁻¹) • o + μ⁻¹ • x = point o x μ := by
    dsimp [point]
    module
  rwa [heq] at h

lemma point_satisfies_cut (f : E →ₗ[ℝ] ℝ) (b : ℝ) (o x : E)
    {μ : ℝ} (hμ : 1 ≤ μ) (hbound : f x - f o ≤ μ * (b - f o)) :
    f (point o x μ) ≤ b := by
  have hpos : 0 < μ := lt_of_lt_of_le zero_lt_one hμ
  have h := mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr hpos.le)
  rw [← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul] at h
  rw [eval_point]
  linarith

lemma point_on_active_cut (f : E →ₗ[ℝ] ℝ) (b : ℝ) (o x : E)
    {μ : ℝ} (hμ : 1 ≤ μ) (hactive : f x - f o = μ * (b - f o)) :
    f (point o x μ) = b := by
  have hpos : 0 < μ := lt_of_lt_of_le zero_lt_one hμ
  rw [eval_point, hactive, ← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul]
  ring

lemma point_at_unit_scale (o x : E) : point o x 1 = x := by
  simp [point]

/-- The largest normalized violation is attained, including the no-cut case.
This uses a maximum over an augmented finite family containing the constant 1. -/
theorem finite_radial_scale_exists {ι : Type*} [Fintype ι] (r : ι → ℝ) :
    ∃ μ : ℝ, 1 ≤ μ ∧ (∀ i, r i ≤ μ) ∧ (μ = 1 ∨ ∃ i, μ = r i) := by
  classical
  let s : Finset ℝ := insert 1 (Finset.univ.image r)
  have hne : s.Nonempty := ⟨1, by simp [s]⟩
  refine ⟨s.max' hne, Finset.le_max' s 1 (by simp [s]), ?_, ?_⟩
  · intro i
    apply Finset.le_max'
    exact Finset.mem_insert.mpr (Or.inr (Finset.mem_image.mpr ⟨i, by simp, rfl⟩))
  · have hm := Finset.max'_mem s hne
    rcases Finset.mem_insert.mp hm with h | h
    · exact Or.inl h
    · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h
      exact Or.inr ⟨i, hi.symm⟩

/-- Normalized dominance gives a point of the final clipped parent.
Strict final-cut slack is explicit; no moving-stage face is used. -/
theorem point_mem_final_clip {ι : Type*}
    (Q : Set E) (hQ : Convex ℝ Q) (f : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ)
    (o x : E) (ho : o ∈ Q) (hx : x ∈ Q)
    (hstrict : ∀ i, f i o < b i) {μ : ℝ} (hμ : 1 ≤ μ)
    (hmax : ∀ i, (f i x - f i o) / (b i - f i o) ≤ μ) :
    point o x μ ∈ Q ∩ {y | ∀ i, f i y ≤ b i} := by
  refine ⟨point_mem_convex Q hQ ho hx hμ, ?_⟩
  intro i
  apply point_satisfies_cut (f i) (b i) o x hμ
  exact (div_le_iff₀ (sub_pos.mpr (hstrict i))).mp (hmax i)

/-- The active row really is a final supporting face, not merely a label. -/
theorem point_mem_active_final_face (f : E →ₗ[ℝ] ℝ) (b : ℝ) (o x : E)
    (hstrict : f o < b) {μ : ℝ} (hμ : 1 ≤ μ)
    (hactive : μ = (f x - f o) / (b - f o)) :
    f (point o x μ) = b := by
  apply point_on_active_cut f b o x hμ
  rw [hactive, div_mul_cancel₀ _ (sub_pos.mpr hstrict).ne']

/-- An affine dominance inequality checked at both ends holds throughout a
cell. This is why the exact checker certifies whole cells, not sampled points. -/
theorem affine_dominance_on_cell {a₀ a₁ b₀ b₁ t : ℝ}
    (h0 : a₀ ≤ b₀) (h1 : a₁ ≤ b₁) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 - t) * a₀ + t * a₁ ≤ (1 - t) * b₀ + t * b₁ := by
  exact add_le_add (mul_le_mul_of_nonneg_left h0 (sub_nonneg.mpr ht1))
    (mul_le_mul_of_nonneg_left h1 ht0)


end HirschRadial
end


-- BEGIN Solutions/PolynomialContinuousRepair.lean

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

noncomputable section

namespace HirschRegionRoute

/-- A connected trace covered by finitely many closed sets forces its endpoint
labels to be connected in the actual set-intersection graph. -/
theorem region_walk_of_preconnected_closed_cover
    {V ι : Type*} [TopologicalSpace V] [Fintype ι]
    (S : ι → Set V) (hc : ∀ i, IsClosed (S i))
    (T : Set V) (hT : IsPreconnected T)
    (hcover : ∀ x ∈ T, ∃ i, x ∈ S i)
    {i j : ι} {u v : V} (huT : u ∈ T) (hvT : v ∈ T)
    (hu : u ∈ S i) (hv : v ∈ S j) :
    Nonempty ((intersectionGraph S).Walk i j) := by
  classical
  by_contra hn
  let A : Set ι := {k | Nonempty ((intersectionGraph S).Walk i k)}
  let U : Set V := ⋃ k, ⋃ (_ : k ∈ A), S k
  let W : Set V := ⋃ k, ⋃ (_ : k ∉ A), S k
  have hU : IsClosed U :=
    isClosed_iUnion_of_finite fun k => isClosed_iUnion_of_finite fun _ => hc k
  have hW : IsClosed W :=
    isClosed_iUnion_of_finite fun k => isClosed_iUnion_of_finite fun _ => hc k
  have hcov : T ⊆ U ∪ W := by
    intro x hx
    obtain ⟨k, hk⟩ := hcover x hx
    by_cases ha : k ∈ A
    · exact Or.inl (mem_iUnion.mpr ⟨k, mem_iUnion.mpr ⟨ha, hk⟩⟩)
    · exact Or.inr (mem_iUnion.mpr ⟨k, mem_iUnion.mpr ⟨ha, hk⟩⟩)
  have hiA : i ∈ A := ⟨.nil⟩
  have hjA : j ∉ A := hn
  obtain ⟨z, _, hzU, hzW⟩ := isPreconnected_closed_iff.mp hT U W hU hW hcov
    ⟨u, huT, mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hiA, hu⟩⟩⟩
    ⟨v, hvT, mem_iUnion.mpr ⟨j, mem_iUnion.mpr ⟨hjA, hv⟩⟩⟩
  obtain ⟨k, hkA, hzk⟩ := mem_iUnion.mp hzU |>.imp fun k h => mem_iUnion.mp h
  obtain ⟨l, hlA, hzl⟩ := mem_iUnion.mp hzW |>.imp fun l h => mem_iUnion.mp h
  obtain ⟨p⟩ := hkA
  obtain ⟨q⟩ := shared_point_walk S hzk hzl
  exact hlA ⟨p.append q⟩

/-- Closed extreme faces covering a connected feasible trace suffice. Ordinary
intersection points become parent vertices by compactness. -/
theorem route_of_preconnected_closed_face_cover
    {d : ℕ} {ι : Type*} [Fintype ι]
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (F : ι → Set (EuclideanSpace ℝ (Fin d))) (B : ι → ℕ)
    (hP : IsCompact P) (hF : ∀ i, IsExtreme ℝ P (F i))
    (hc : ∀ i, IsClosed (F i)) (hD : ∀ i, DiamLE (F i) (B i))
    (T : Set (EuclideanSpace ℝ (Fin d))) (hT : IsPreconnected T)
    (hcover : ∀ x ∈ T, ∃ i, x ∈ F i)
    (u v : EuclideanSpace ℝ (Fin d))
    (huT : u ∈ T) (hvT : v ∈ T)
    (huP : u ∈ extremePoints ℝ P) (hvP : v ∈ extremePoints ℝ P) :
    Route (Adj P) (∑ i, B i) u v := by
  obtain ⟨i, hui⟩ := hcover u huT
  obtain ⟨j, hvj⟩ := hcover v hvT
  obtain ⟨p⟩ := region_walk_of_preconnected_closed_cover F hc T hT hcover huT hvT hui hvj
  let S := fun i => extremePoints ℝ P ∩ F i
  have q : Nonempty ((intersectionGraph S).Walk i j) := by
    clear hui hvj
    induction p with
    | nil => exact ⟨.nil⟩
    | @cons a b c hab p ih =>
      obtain ⟨x, hxa, hxb⟩ := hab.2
      obtain ⟨z, hzP, hza, hzb⟩ := compact_faces_shared_point_portal
        P (F a) (F b) hP (hF a) (hF b) (hc a) (hc b) x hxa hxb
      obtain ⟨q⟩ := ih
      exact ⟨.cons ⟨hab.1, z, ⟨hzP, hza⟩, ⟨hzP, hzb⟩⟩ q⟩
  exact route_of_connected_regions (Adj P) S B
    (fun k => extreme_face_region P (F k) (B k) (hF k) (hD k))
    q u v ⟨huP, hui⟩ ⟨hvP, hvj⟩


end HirschRegionRoute

namespace HirschRadial

/-- A finite maximum including the constant one. -/
def gauge {V ι : Type*} : List ι → (ι → V → ℝ) → V → ℝ
  | [], _, _ => 1
  | i :: l, r, x => max (r i x) (gauge l r x)

lemma gauge_ge_one {V ι : Type*} (l : List ι) (r : ι → V → ℝ) (x : V) :
    1 ≤ gauge l r x := by
  induction l with
  | nil => exact le_rfl
  | cons i l ih => exact ih.trans (le_max_right _ _)

lemma le_gauge {V ι : Type*} (l : List ι) (r : ι → V → ℝ) (x : V)
    {i : ι} (hi : i ∈ l) : r i x ≤ gauge l r x := by
  induction l with
  | nil => simp at hi
  | cons j l ih =>
    rcases List.mem_cons.mp hi with rfl | hi
    · exact le_max_left _ _
    · exact (ih hi).trans (le_max_right _ _)

lemma gauge_attains {V ι : Type*} (l : List ι) (r : ι → V → ℝ) (x : V) :
    gauge l r x = 1 ∨ ∃ i ∈ l, gauge l r x = r i x := by
  induction l with
  | nil => exact Or.inl rfl
  | cons i l ih =>
    by_cases h : r i x ≤ gauge l r x
    · rw [gauge, max_eq_right h]
      rcases ih with h1 | ⟨j, hj, heq⟩
      · exact Or.inl h1
      · exact Or.inr ⟨j, List.mem_cons_of_mem i hj, heq⟩
    · rw [gauge, max_eq_left (le_of_not_ge h)]
      exact Or.inr ⟨i, by simp, rfl⟩

lemma gauge_eq_one {V ι : Type*} (l : List ι) (r : ι → V → ℝ) (x : V)
    (h : ∀ i ∈ l, r i x ≤ 1) : gauge l r x = 1 := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    rw [gauge, ih (fun j hj => h j (List.mem_cons_of_mem i hj))]
    exact max_eq_right (h i (by simp))

lemma continuous_gauge {V ι : Type*} [TopologicalSpace V]
    (l : List ι) (r : ι → V → ℝ) (h : ∀ i, Continuous (r i)) :
    Continuous (gauge l r) := by
  induction l with
  | nil => exact continuous_const
  | cons i l ih => exact (h i).max ih

variable {d : ℕ} {ι : Type*} [Fintype ι]

abbrev ClipSpace (d : ℕ) := EuclideanSpace ℝ (Fin d)

def finalClip (Q : Set (ClipSpace d)) (f : ι → ClipSpace d →L[ℝ] ℝ) (b : ι → ℝ) :=
  Q ∩ {x | ∀ i, f i x ≤ b i}

def normalized (f : ι → ClipSpace d →L[ℝ] ℝ) (b : ι → ℝ) (o : ClipSpace d)
    (i : ι) (x : ClipSpace d) : ℝ := (f i x - f i o) / (b i - f i o)

def scale (f : ι → ClipSpace d →L[ℝ] ℝ) (b : ι → ℝ) (o x : ClipSpace d) : ℝ :=
  gauge Finset.univ.toList (normalized f b o) x

def retract (f : ι → ClipSpace d →L[ℝ] ℝ) (b : ι → ℝ) (o x : ClipSpace d) : ClipSpace d :=
  point o x (scale f b o x)

lemma scale_ge_one (f : ι → ClipSpace d →L[ℝ] ℝ) (b : ι → ℝ) (o x : ClipSpace d) :
    1 ≤ scale f b o x := gauge_ge_one _ _ _

lemma normalized_le_scale (f : ι → ClipSpace d →L[ℝ] ℝ) (b : ι → ℝ)
    (o x : ClipSpace d) (i : ι) : normalized f b o i x ≤ scale f b o x := by
  apply le_gauge
  simp

lemma continuous_scale (f : ι → ClipSpace d →L[ℝ] ℝ) (b : ι → ℝ) (o : ClipSpace d) :
    Continuous (scale f b o) := by
  apply continuous_gauge
  intro i
  exact ((f i).continuous.sub continuous_const).div_const _

lemma continuous_retract (f : ι → ClipSpace d →L[ℝ] ℝ) (b : ι → ℝ) (o : ClipSpace d) :
    Continuous (retract f b o) := by
  have hi : Continuous (fun x => (scale f b o x)⁻¹) :=
    (continuous_scale f b o).inv₀ fun x => ne_of_gt (lt_of_lt_of_le zero_lt_one (scale_ge_one f b o x))
  exact continuous_const.add (hi.smul (continuous_id.sub continuous_const))

lemma retract_mem (Q : Set (ClipSpace d)) (hQ : Convex ℝ Q)
    (f : ι → ClipSpace d →L[ℝ] ℝ) (b : ι → ℝ) (o x : ClipSpace d)
    (ho : o ∈ Q) (hx : x ∈ Q) (hs : ∀ i, f i o < b i) :
    retract f b o x ∈ finalClip Q f b :=
  point_mem_final_clip Q hQ (fun i => (f i).toLinearMap) b o x ho hx hs
    (scale_ge_one f b o x) (normalized_le_scale f b o x)

lemma retract_fixes (Q : Set (ClipSpace d))
    (f : ι → ClipSpace d →L[ℝ] ℝ) (b : ι → ℝ) (o x : ClipSpace d)
    (hs : ∀ i, f i o < b i) (hx : x ∈ finalClip Q f b) :
    retract f b o x = x := by
  have hm : scale f b o x = 1 := by
    apply gauge_eq_one
    intro i _
    apply (div_le_iff₀ (sub_pos.mpr (hs i))).mpr
    simpa using sub_le_sub_right (hx.2 i) (f i o)
  change point o x (scale f b o x) = x
  rw [hm, point_at_unit_scale]

lemma retract_eq_self_or_on_cut
    (f : ι → ClipSpace d →L[ℝ] ℝ) (b : ι → ℝ) (o x : ClipSpace d)
    (hs : ∀ i, f i o < b i) :
    retract f b o x = x ∨ ∃ i, f i (retract f b o x) = b i := by
  rcases gauge_attains Finset.univ.toList (normalized f b o) x with h | ⟨i, _, hi⟩
  · left
    change point o x (scale f b o x) = x
    rw [show scale f b o x = 1 from h, point_at_unit_scale]
  · right
    exact ⟨i, point_mem_active_final_face (f i).toLinearMap (b i) o x (hs i)
      (scale_ge_one f b o x) hi⟩


end HirschRadial
end


-- BEGIN Solutions/PolynomialSimultaneousClipping.lean

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

noncomputable section

namespace HirschRadial

variable {d : ℕ}

lemma segment_collinear (a b : ClipSpace d) : Collinear ℝ (segment ℝ a b) := by
  rw [collinear_iff_exists_forall_eq_smul_vadd]
  refine ⟨a, b - a, ?_⟩
  intro x hx
  obtain ⟨s, t, _, _, hst, rfl⟩ := hx
  refine ⟨t, ?_⟩
  change s • a + t • b = t • (b - a) + a
  have hs : s = 1 - t := by linarith
  rw [hs]
  module

/-- Any convex collinear set has graph diameter at most one, even without
compactness. If it has two distinct extreme points, they span the entire set. -/
theorem diamLE_one_of_convex_collinear
    (S : Set (ClipSpace d)) (hS : Convex ℝ S) (hcol : Collinear ℝ S) : DiamLE S 1 := by
  intro u hu v hv
  by_cases huv : u = v
  · exact HirschRegionRoute.route_one (Adj S) (Or.inl huv)
  have hEq : S = segment ℝ u v := by
    apply Subset.antisymm ?_ (hS.segment_subset hu.1 hv.1)
    intro x hx
    have h3 : Collinear ℝ ({u, x, v} : Set (ClipSpace d)) :=
      hcol.subset (by simp only [insert_subset_iff, singleton_subset_iff]; exact ⟨hu.1, hx, hv.1⟩)
    rcases h3.wbtw_or_wbtw_or_wbtw with h | h | h
    · exact h.mem_segment
    · rcases (mem_extremePoints_iff_forall_segment.mp hv).2 x hx u hu.1 h.mem_segment with h | h
      · simpa [h] using (right_mem_segment ℝ u v)
      · exact False.elim (huv h)
    · rcases (mem_extremePoints_iff_forall_segment.mp hu).2 v hv.1 x hx h.mem_segment with h | h
      · exact False.elim (huv h.symm)
      · simpa [h] using (left_mem_segment ℝ u v)
  apply HirschRegionRoute.route_one (Adj S)
  right
  refine ⟨huv, ?_⟩
  rw [← hEq]
  exact IsExtreme.refl ℝ S

/-- Clipping an old edge produces a closed extreme face of diameter at most
one. The same proof covers a retained singleton and an empty clipped edge. -/
theorem clipped_segment_face
    (P Q : Set (ClipSpace d)) (hPQ : P ⊆ Q) (hP : IsCompact P) (hPc : Convex ℝ P)
    (a b : ClipSpace d) (hE : IsExtreme ℝ Q (segment ℝ a b)) :
    IsExtreme ℝ P (P ∩ segment ℝ a b) ∧
      IsClosed (P ∩ segment ℝ a b) ∧ DiamLE (P ∩ segment ℝ a b) 1 := by
  have hclosed : IsClosed (segment ℝ a b) := by
    rw [segment_eq_image]
    exact (isCompact_Icc.image (by fun_prop)).isClosed
  refine ⟨?_, hP.isClosed.inter hclosed, ?_⟩
  · refine ⟨inter_subset_left, ?_⟩
    intro x hx y hy z hz hseg
    exact ⟨hx, hE.left_mem_of_mem_openSegment (hPQ hx) (hPQ hy) hz.2 hseg⟩
  · exact diamLE_one_of_convex_collinear _ (hPc.inter (convex_segment a b))
      ((segment_collinear a b).subset inter_subset_right)

lemma supporting_cut_extreme
    (P : Set (ClipSpace d)) (f : ClipSpace d →L[ℝ] ℝ) (c : ℝ)
    (hbound : ∀ x ∈ P, f x ≤ c) : IsExtreme ℝ P (P ∩ {x | f x = c}) := by
  refine ⟨inter_subset_left, ?_⟩
  intro x hx y hy z hz hseg
  refine ⟨hx, ?_⟩
  by_contra hne
  have hlt : f x < c := lt_of_le_of_ne (hbound x hx) hne
  obtain ⟨a, b, ha, hb, hab, he⟩ := hseg
  have he' := congrArg f he
  simp only [map_add, map_smul, smul_eq_mul] at he'
  rw [hz.2] at he'
  have hlt' := add_lt_add_of_lt_of_le
    (mul_lt_mul_of_pos_left hlt ha)
    (mul_le_mul_of_nonneg_left (hbound y hy) hb.le)
  rw [← add_mul, hab, one_mul] at hlt'
  linarith

variable {ι : Type*} [Fintype ι]

lemma finalClip_convex (Q : Set (ClipSpace d)) (hQ : Convex ℝ Q)
    (f : ι → ClipSpace d →L[ℝ] ℝ) (b : ι → ℝ) : Convex ℝ (finalClip Q f b) := by
  intro x hx y hy a c ha hc hac
  refine ⟨hQ hx.1 hy.1 ha hc hac, ?_⟩
  intro i
  simp only [map_add, map_smul, smul_eq_mul]
  calc
    a * f i x + c * f i y ≤ a * b i + c * b i :=
      add_le_add (mul_le_mul_of_nonneg_left (hx.2 i) ha) (mul_le_mul_of_nonneg_left (hy.2 i) hc)
    _ = b i := by rw [← add_mul, hac, one_mul]

/-- The complete geometric trace of an old walk, including the zero-step case. -/
def edgeTrace (w : ℕ → ClipSpace d) : ℕ → Set (ClipSpace d)
  | 0 => {w 0}
  | L + 1 => edgeTrace w L ∪ segment ℝ (w L) (w (L + 1))

lemma edgeTrace_start (w : ℕ → ClipSpace d) (L : ℕ) : w 0 ∈ edgeTrace w L := by
  induction L with
  | zero => rfl
  | succ L ih => exact Or.inl ih

lemma edgeTrace_end (w : ℕ → ClipSpace d) (L : ℕ) : w L ∈ edgeTrace w L := by
  cases L with
  | zero => rfl
  | succ L => exact Or.inr (right_mem_segment ℝ _ _)

lemma edgeTrace_preconnected (w : ℕ → ClipSpace d) (L : ℕ) :
    IsPreconnected (edgeTrace w L) := by
  induction L with
  | zero => exact isPreconnected_singleton
  | succ L ih =>
    exact ih.union' ⟨w L, edgeTrace_end w L, left_mem_segment ℝ _ _⟩
      (convex_segment _ _).isPreconnected

lemma edgeTrace_cases (w : ℕ → ClipSpace d) (L : ℕ) {x : ClipSpace d}
    (hx : x ∈ edgeTrace w L) : x = w 0 ∨ ∃ k < L, x ∈ segment ℝ (w k) (w (k + 1)) := by
  induction L with
  | zero => exact Or.inl hx
  | succ L ih =>
    rcases hx with hx | hx
    · rcases ih hx with h | ⟨k, hk, hx⟩
      · exact Or.inl h
      · exact Or.inr ⟨k, by omega, hx⟩
    · exact Or.inr ⟨L, by omega, hx⟩

lemma edgeTrace_covered (w : ℕ → ClipSpace d) (L : ℕ) (hL : 0 < L)
    {x : ClipSpace d} (hx : x ∈ edgeTrace w L) :
    ∃ k : Fin L, x ∈ segment ℝ (w k) (w (k + 1)) := by
  rcases edgeTrace_cases w L hx with h | ⟨k, hk, hx⟩
  · exact ⟨⟨0, hL⟩, h ▸ left_mem_segment ℝ _ _⟩
  · exact ⟨⟨k, hk⟩, hx⟩

/-- End-to-end simultaneous clipping. Every final cut face is charged once,
not once per old-edge crossing or deformation event. The old walk may contain
stays. Q need only be convex, P compact, and the centre strictly feasible for
the added cuts. No finite-cell cover is assumed: continuity constructs the
needed connected trace and actual fixed-parent support intersections. -/
theorem simultaneous_clip_route
    (Q : Set (ClipSpace d)) (hQ : Convex ℝ Q)
    (f : ι → ClipSpace d →L[ℝ] ℝ) (b : ι → ℝ)
    (o : ClipSpace d) (ho : o ∈ Q) (hs : ∀ i, f i o < b i)
    (hP : IsCompact (finalClip Q f b))
    (B : ι → ℕ) (hB : ∀ i, DiamLE (finalClip Q f b ∩ {x | f i x = b i}) (B i))
    (w : ℕ → ClipSpace d) (L : ℕ)
    (hverts : ∀ k ≤ L, w k ∈ extremePoints ℝ Q)
    (hsteps : ∀ k < L, w k = w (k + 1) ∨ Adj Q (w k) (w (k + 1)))
    (h0 : w 0 ∈ extremePoints ℝ (finalClip Q f b))
    (hL : w L ∈ extremePoints ℝ (finalClip Q f b)) :
    HirschRegionRoute.Route (Adj (finalClip Q f b)) (L + ∑ i, B i) (w 0) (w L) := by
  classical
  by_cases hzero : L = 0
  · subst L
    exact ⟨fun _ => w 0, rfl, rfl, fun _ _ => Or.inl rfl⟩
  have hpos : 0 < L := Nat.pos_of_ne_zero hzero
  let P := finalClip Q f b
  let F : Sum (Fin L) ι → Set (ClipSpace d) :=
    Sum.elim (fun k => P ∩ segment ℝ (w k) (w (k + 1)))
      (fun i => P ∩ {x | f i x = b i})
  let C : Sum (Fin L) ι → ℕ := Sum.elim (fun _ => 1) B
  have hPc : Convex ℝ P := finalClip_convex Q hQ f b
  have hOld : ∀ k : Fin L,
      IsExtreme ℝ P (F (.inl k)) ∧ IsClosed (F (.inl k)) ∧ DiamLE (F (.inl k)) 1 := by
    intro k
    apply clipped_segment_face P Q (fun _ hx => hx.1) hP hPc
    rcases hsteps k k.isLt with h | h
    · rw [h, segment_same]
      exact isExtreme_singleton.mpr (hverts (k + 1) (by omega))
    · exact h.2
  have hFace : ∀ k, IsExtreme ℝ P (F k) := by
    intro k
    cases k with
    | inl k => exact (hOld k).1
    | inr i => exact supporting_cut_extreme P (f i) (b i) (fun x hx => hx.2 i)
  have hClosed : ∀ k, IsClosed (F k) := by
    intro k
    cases k with
    | inl k => exact (hOld k).2.1
    | inr i => exact hP.isClosed.inter (isClosed_eq (f i).continuous continuous_const)
  have hDiam : ∀ k, DiamLE (F k) (C k) := by
    intro k
    cases k with
    | inl k => exact (hOld k).2.2
    | inr i => exact hB i
  have hTraceQ : ∀ x ∈ edgeTrace w L, x ∈ Q := by
    intro x hx
    obtain ⟨k, hk⟩ := edgeTrace_covered w L hpos hx
    exact hQ.segment_subset (hverts k (by omega)).1 (hverts (k + 1) (by omega)).1 hk
  let T := retract f b o '' edgeTrace w L
  have hT : IsPreconnected T :=
    (edgeTrace_preconnected w L).image _ (continuous_retract f b o).continuousOn
  have hCover : ∀ y ∈ T, ∃ k, y ∈ F k := by
    rintro y ⟨x, hx, rfl⟩
    have hyP := retract_mem Q hQ f b o x ho (hTraceQ x hx) hs
    rcases retract_eq_self_or_on_cut f b o x hs with heq | ⟨i, hi⟩
    · obtain ⟨k, hk⟩ := edgeTrace_covered w L hpos hx
      exact ⟨.inl k, hyP, heq.symm ▸ hk⟩
    · exact ⟨.inr i, hyP, hi⟩
  have huT : w 0 ∈ T := ⟨w 0, edgeTrace_start w L, retract_fixes Q f b o (w 0) hs h0.1⟩
  have hvT : w L ∈ T := ⟨w L, edgeTrace_end w L, retract_fixes Q f b o (w L) hs hL.1⟩
  have hr := HirschRegionRoute.route_of_preconnected_closed_face_cover
    P F C hP hFace hClosed hDiam T hT hCover (w 0) (w L) huT hvT h0 hL
  simpa [C, Fintype.sum_sum_type] using hr


end HirschRadial
end


-- BEGIN Solutions/PolynomialClippingAttachments.lean

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

noncomputable section
namespace HirschRadial

variable {d : ℕ} {ι : Type*} [Fintype ι]

/-- A vertex strictly inside all added halfspaces was already an outer vertex.
A common small homothety makes both ends of any proposed outer segment feasible. -/
theorem extreme_outer_of_strict_cuts
    (Q : Set (ClipSpace d)) (hQ : Convex ℝ Q)
    (f : ι → ClipSpace d →L[ℝ] ℝ) (b : ι → ℝ) (x : ClipSpace d)
    (hx : x ∈ extremePoints ℝ (finalClip Q f b))
    (hsx : ∀ i, f i x < b i) : x ∈ extremePoints ℝ Q := by
  refine ⟨hx.1.1, ?_⟩
  intro y hy z hz hopen
  let μ := max (scale f b x y) (scale f b x z)
  have hμ : 1 ≤ μ := (scale_ge_one f b x y).trans (le_max_left _ _)
  have hyP : point x y μ ∈ finalClip Q f b :=
    point_mem_final_clip Q hQ (fun i => (f i).toLinearMap) b x y hx.1.1 hy hsx hμ
      (fun i => (normalized_le_scale f b x y i).trans (le_max_left _ _))
  have hzP : point x z μ ∈ finalClip Q f b :=
    point_mem_final_clip Q hQ (fun i => (f i).toLinearMap) b x z hx.1.1 hz hsx hμ
      (fun i => (normalized_le_scale f b x z i).trans (le_max_right _ _))
  have hopen' : x ∈ openSegment ℝ (point x y μ) (point x z μ) := by
    obtain ⟨a, c, ha, hc, hac, he⟩ := hopen
    refine ⟨a, c, ha, hc, hac, ?_⟩
    dsimp [point]
    calc
      a • (x + μ⁻¹ • (y - x)) + c • (x + μ⁻¹ • (z - x)) =
          (a + c) • x + μ⁻¹ • (a • y + c • z - (a + c) • x) := by module
      _ = x := by rw [hac, one_smul, he]; simp
  have he := hx.2 hyP hzP hopen'
  change x + μ⁻¹ • (y - x) = x at he
  have hsmul : μ⁻¹ • (y - x) = 0 := add_left_cancel (he.trans (add_zero x).symm)
  have hμ0 : μ ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hμ)
  exact sub_eq_zero.mp ((smul_eq_zero.mp hsmul).resolve_left (inv_ne_zero hμ0))

/-- Every new vertex lies on an actual final cut. -/
theorem extreme_outer_or_on_final_cut
    (Q : Set (ClipSpace d)) (hQ : Convex ℝ Q)
    (f : ι → ClipSpace d →L[ℝ] ℝ) (b : ι → ℝ) (x : ClipSpace d)
    (hx : x ∈ extremePoints ℝ (finalClip Q f b)) :
    x ∈ extremePoints ℝ Q ∨ ∃ i, f i x = b i := by
  classical
  by_cases h : ∃ i, f i x = b i
  · exact Or.inr h
  · left
    apply extreme_outer_of_strict_cuts Q hQ f b x hx
    intro i
    have hne : f i x ≠ b i := fun hi => h ⟨i, hi⟩
    exact lt_of_le_of_ne (hx.1.2 i) hne

/-- A linear functional reaches its outer maximum at an outer extreme point. -/
theorem outer_vertex_above
    (Q : Set (ClipSpace d)) (hQ : IsCompact Q)
    (g : ClipSpace d →L[ℝ] ℝ) (x : ClipSpace d) (hx : x ∈ Q) :
    ∃ a, a ∈ extremePoints ℝ Q ∧ g x ≤ g a := by
  obtain ⟨z, hz, hmax⟩ := hQ.exists_isMaxOn ⟨x, hx⟩ g.continuous.continuousOn
  have hF := supporting_cut_extreme Q g (g z) (fun y hy => hmax hy)
  have hFc : IsClosed (Q ∩ {y | g y = g z}) :=
    hQ.isClosed.inter (isClosed_eq g.continuous continuous_const)
  obtain ⟨a, ha, haF⟩ := HirschRegionRoute.compact_face_point_has_parent_vertex
    Q (Q ∩ {y | g y = g z}) hQ hF hFc ⟨z, hz, rfl⟩
  exact ⟨a, ha, (hmax hx).trans_eq haF.2.symm⟩

/-- A segment going outward through one active cut retracts entirely into the
union of final cut faces. The active label may change, but the family is fixed. -/
theorem outward_segment_retract_on_cut
    (Q : Set (ClipSpace d)) (hQ : Convex ℝ Q)
    (f : ι → ClipSpace d →L[ℝ] ℝ) (b : ι → ℝ)
    (o : ClipSpace d) (ho : o ∈ Q) (hs : ∀ i, f i o < b i)
    (u a : ClipSpace d) (hu : u ∈ finalClip Q f b) (ha : a ∈ Q)
    (i : ι) (hui : f i u = b i) (hai : b i ≤ f i a)
    (x : ClipSpace d) (hx : x ∈ segment ℝ u a) :
    ∃ j, retract f b o x ∈ finalClip Q f b ∧ f j (retract f b o x) = b j := by
  have hxQ : x ∈ Q := hQ.segment_subset hu.1 ha hx
  have hxP := retract_mem Q hQ f b o x ho hxQ hs
  have hge : b i ≤ f i x := by
    obtain ⟨s, t, hs0, ht0, hst, he⟩ := hx
    have he' := congrArg (f i) he
    simp only [map_add, map_smul, smul_eq_mul] at he'
    rw [hui] at he'
    calc
      b i = (s + t) * b i := by rw [hst, one_mul]
      _ = s * b i + t * b i := add_mul _ _ _
      _ ≤ s * b i + t * f i a :=
        add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hai ht0)
      _ = f i x := he'
  rcases retract_eq_self_or_on_cut f b o x hs with he | ⟨j, hj⟩
  · refine ⟨i, hxP, ?_⟩
    rw [he]
    have hle : f i x ≤ b i := by simpa [he] using hxP.2 i
    exact le_antisymm hle hge
  · exact ⟨j, hxP, hj⟩

/-- Every final vertex attaches to the radial image of an outer vertex using
only final cut faces; an already outer vertex needs no attachment at all. -/
theorem final_vertex_attachment
    (Q : Set (ClipSpace d)) (hQ : Convex ℝ Q) (hQc : IsCompact Q)
    (f : ι → ClipSpace d →L[ℝ] ℝ) (b : ι → ℝ)
    (o : ClipSpace d) (ho : o ∈ Q) (hs : ∀ i, f i o < b i)
    (u : ClipSpace d) (hu : u ∈ extremePoints ℝ (finalClip Q f b)) :
    ∃ a, a ∈ extremePoints ℝ Q ∧
      (u = a ∨ ∀ x ∈ segment ℝ u a,
        ∃ i, retract f b o x ∈ finalClip Q f b ∧ f i (retract f b o x) = b i) := by
  rcases extreme_outer_or_on_final_cut Q hQ f b u hu with huQ | ⟨i, hi⟩
  · exact ⟨u, huQ, Or.inl rfl⟩
  · obtain ⟨a, ha, hab⟩ := outer_vertex_above Q hQc (f i) u hu.1.1
    refine ⟨a, ha, Or.inr ?_⟩
    intro x hx
    apply outward_segment_retract_on_cut Q hQ f b o ho hs u a hu.1 ha.1 i hi
    · simpa [hi] using hab
    · exact hx

/-- Stays contribute no new points to the geometric trace. Only genuine old
edges and the initial vertex are needed as supports. -/
lemma edgeTrace_edge_or_start
    (Q : Set (ClipSpace d)) (w : ℕ → ClipSpace d) (L : ℕ)
    (hsteps : ∀ k < L, w k = w (k + 1) ∨ Adj Q (w k) (w (k + 1)))
    {x : ClipSpace d} (hx : x ∈ edgeTrace w L) :
    x = w 0 ∨ ∃ k < L, Adj Q (w k) (w (k + 1)) ∧ x ∈ segment ℝ (w k) (w (k + 1)) := by
  induction L with
  | zero => exact Or.inl hx
  | succ L ih =>
    have hp : ∀ k < L, w k = w (k + 1) ∨ Adj Q (w k) (w (k + 1)) :=
      fun k hk => hsteps k (by omega)
    rcases hx with hx | hx
    · rcases ih hp hx with h | ⟨k, hk, hE, hx⟩
      · exact Or.inl h
      · exact Or.inr ⟨k, by omega, hE, hx⟩
    · rcases hsteps L (by omega) with he | hE
      · have hx' : x = w L := by simpa [← he] using hx
        have hxT : x ∈ edgeTrace w L := hx'.symm ▸ edgeTrace_end w L
        rcases ih hp hxT with h | ⟨k, hk, hE, hx⟩
        · exact Or.inl h
        · exact Or.inr ⟨k, by omega, hE, hx⟩
      · exact Or.inr ⟨L, by omega, hE, hx⟩


end HirschRadial
end


-- BEGIN Solutions/PolynomialExteriorCapClipping.lean

/-! Exterior-cap shortcuts for simultaneous clipping.

The cap is a genuine convex subset of the compact truncated outer parent and
is disjoint from the FINAL polytope. All cap motion retracts to the already
charged final cut faces. No diameter budget for the cap is assumed.
-/

open scoped BigOperators RealInnerProductSpace
open Set Hirsch HirschRadial HirschRegionRoute

noncomputable section
namespace HirschExterior

variable {d : ℕ} {ι : Type*} [Fintype ι]

/-- Any outer point absent from the final clip retracts to a final cut face. -/
lemma retract_on_cut_of_exterior
    (Q : Set (ClipSpace d)) (hQ : Convex ℝ Q)
    (f : ι → ClipSpace d →L[ℝ] ℝ) (b : ι → ℝ)
    (o : ClipSpace d) (ho : o ∈ Q) (hs : ∀ i, f i o < b i)
    (x : ClipSpace d) (hx : x ∈ Q) (hout : x ∉ finalClip Q f b) :
    ∃ i, retract f b o x ∈ finalClip Q f b ∧ f i (retract f b o x) = b i := by
  have hy := retract_mem Q hQ f b o x ho hx hs
  rcases retract_eq_self_or_on_cut f b o x hs with he | ⟨i, hi⟩
  · exact False.elim (hout (he ▸ hy))
  · exact ⟨i, hy, hi⟩

/-- A convex exterior cap gives genuine connected traces on the union of
final cut faces, with no intrinsic cap-diameter assumption. -/
theorem exterior_cap_trace
    (Q G : Set (ClipSpace d)) (hQ : Convex ℝ Q) (hG : Convex ℝ G)
    (hGQ : G ⊆ Q) (f : ι → ClipSpace d →L[ℝ] ℝ) (b : ι → ℝ)
    (o : ClipSpace d) (ho : o ∈ Q) (hs : ∀ i, f i o < b i)
    (hout : ∀ x ∈ G, x ∉ finalClip Q f b) :
    IsPreconnected (retract f b o '' G) ∧
      ∀ y ∈ retract f b o '' G,
        ∃ i, y ∈ finalClip Q f b ∩ {x | f i x = b i} := by
  refine ⟨hG.isPreconnected.image _ (continuous_retract f b o).continuousOn, ?_⟩
  rintro y ⟨x, hx, rfl⟩
  exact retract_on_cut_of_exterior Q hQ f b o ho hs x (hGQ hx) (hout x hx)

/-- An exterior jump may be a long segment in the cap. Stays add no new
points; other trace points belong to genuine outer edges or to the cap. -/
lemma exterior_edgeTrace_cases
    (Q G : Set (ClipSpace d)) (hG : Convex ℝ G)
    (w : ℕ → ClipSpace d) (L : ℕ)
    (hsteps : ∀ k < L, w k = w (k + 1) ∨
      Adj Q (w k) (w (k + 1)) ∨ (w k ∈ G ∧ w (k + 1) ∈ G))
    {x : ClipSpace d} (hx : x ∈ edgeTrace w L) :
    x = w 0 ∨ (∃ k < L, Adj Q (w k) (w (k + 1)) ∧
      x ∈ segment ℝ (w k) (w (k + 1))) ∨ x ∈ G := by
  induction L with
  | zero => exact Or.inl hx
  | succ L ih =>
    have hp : ∀ k < L, w k = w (k + 1) ∨
        Adj Q (w k) (w (k + 1)) ∨ (w k ∈ G ∧ w (k + 1) ∈ G) :=
      fun k hk => hsteps k (by omega)
    have lift : x = w 0 ∨ (∃ k < L, Adj Q (w k) (w (k + 1)) ∧
        x ∈ segment ℝ (w k) (w (k + 1))) ∨ x ∈ G →
        x = w 0 ∨ (∃ k < L + 1, Adj Q (w k) (w (k + 1)) ∧
        x ∈ segment ℝ (w k) (w (k + 1))) ∨ x ∈ G := by
      rintro (h | ⟨k, hk, he, hx⟩ | hg)
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨k, by omega, he, hx⟩)
      · exact Or.inr (Or.inr hg)
    rcases hx with hx | hx
    · exact lift (ih hp hx)
    · rcases hsteps L (by omega) with he | hE | hcap
      · have hx' : x = w L := by simpa [← he] using hx
        exact lift (ih hp (hx'.symm ▸ edgeTrace_end w L))
      · exact Or.inr (Or.inl ⟨L, by omega, hE, hx⟩)
      · exact Or.inr (Or.inr (hG.segment_subset hcap.1 hcap.2 hx))

/-- Full endpoint-attachment assembly allowing arbitrary shortcuts inside one
convex exterior cap. Only genuine edges supply clipped-edge supports. The
cap itself is never a paid region of the final parent. -/
theorem clip_route_with_exterior_attachments
    (Q G : Set (ClipSpace d)) (hQ : Convex ℝ Q) (hG : Convex ℝ G) (hGQ : G ⊆ Q)
    (f : ι → ClipSpace d →L[ℝ] ℝ) (b : ι → ℝ)
    (o : ClipSpace d) (ho : o ∈ Q) (hs : ∀ i, f i o < b i)
    (hP : IsCompact (finalClip Q f b))
    (hout : ∀ x ∈ G, x ∉ finalClip Q f b)
    (B : ι → ℕ) (hB : ∀ i, DiamLE (finalClip Q f b ∩ {x | f i x = b i}) (B i))
    (u v : ClipSpace d)
    (hu : u ∈ extremePoints ℝ (finalClip Q f b))
    (hv : v ∈ extremePoints ℝ (finalClip Q f b))
    (w : ℕ → ClipSpace d) (L : ℕ) (h0Q : w 0 ∈ extremePoints ℝ Q)
    (hsteps : ∀ k < L, w k = w (k + 1) ∨
      Adj Q (w k) (w (k + 1)) ∨ (w k ∈ G ∧ w (k + 1) ∈ G))
    (hAu : u = w 0 ∨ ∀ x ∈ segment ℝ u (w 0),
      ∃ i, retract f b o x ∈ finalClip Q f b ∧ f i (retract f b o x) = b i)
    (hAv : v = w L ∨ ∀ x ∈ segment ℝ v (w L),
      ∃ i, retract f b o x ∈ finalClip Q f b ∧ f i (retract f b o x) = b i) :
    Route (Adj (finalClip Q f b)) (L + ∑ i, B i) u v := by
  classical
  let P := finalClip Q f b
  let E : Option (Fin L) → Set (ClipSpace d) := fun k =>
    k.elim (P ∩ {w 0}) (fun k =>
      if Adj Q (w k) (w (k + 1)) then P ∩ segment ℝ (w k) (w (k + 1)) else ∅)
  let F : Sum (Option (Fin L)) ι → Set (ClipSpace d) :=
    Sum.elim E (fun i => P ∩ {x | f i x = b i})
  let C : Sum (Option (Fin L)) ι → ℕ :=
    Sum.elim (fun k => k.elim 0 (fun _ => 1)) B
  have hPc : Convex ℝ P := finalClip_convex Q hQ f b
  have hOld : ∀ k : Option (Fin L),
      IsExtreme ℝ P (E k) ∧ IsClosed (E k) ∧ DiamLE (E k) (k.elim 0 (fun _ => 1)) := by
    intro k
    cases k with
    | none =>
      have hS : IsExtreme ℝ Q {w 0} := isExtreme_singleton.mpr h0Q
      refine ⟨⟨inter_subset_left, ?_⟩, hP.isClosed.inter isClosed_singleton, ?_⟩
      · intro x hx y hy z hz hseg
        exact ⟨hx, hS.left_mem_of_mem_openSegment hx.1 hy.1 hz.2 hseg⟩
      · intro x hx y hy
        have he : x = y := (show x = w 0 from hx.1.2).trans (show y = w 0 from hy.1.2).symm
        exact ⟨fun _ => x, rfl, he, by intro k hk; change k < 0 at hk; omega⟩
    | some k =>
      by_cases h : Adj Q (w k) (w (k + 1))
      · simpa [E, h] using clipped_segment_face P Q (fun _ hx => hx.1) hP hPc (w k) (w (k + 1)) h.2
      · have he : IsExtreme ℝ P (∅ : Set (ClipSpace d)) :=
          ⟨empty_subset _, by intro x hx y hy z hz; exact False.elim hz⟩
        have hd : DiamLE (∅ : Set (ClipSpace d)) 1 := by
          intro x hx
          exact False.elim hx.1
        simpa [E, h] using (show IsExtreme ℝ P (∅ : Set (ClipSpace d)) ∧
          IsClosed (∅ : Set (ClipSpace d)) ∧ DiamLE (∅ : Set (ClipSpace d)) 1 from ⟨he, isClosed_empty, hd⟩)
  have hFace : ∀ k, IsExtreme ℝ P (F k) := by
    intro k
    cases k with
    | inl k => exact (hOld k).1
    | inr i => exact supporting_cut_extreme P (f i) (b i) (fun x hx => hx.2 i)
  have hClosed : ∀ k, IsClosed (F k) := by
    intro k
    cases k with
    | inl k => exact (hOld k).2.1
    | inr i => exact hP.isClosed.inter (isClosed_eq (f i).continuous continuous_const)
  have hDiam : ∀ k, DiamLE (F k) (C k) := by
    intro k
    cases k with
    | inl k => exact (hOld k).2.2
    | inr i => exact hB i
  have hMidQ : ∀ x ∈ edgeTrace w L, x ∈ Q := by
    intro x hx
    rcases exterior_edgeTrace_cases Q G hG w L hsteps hx with he | ⟨k, hk, hE, hx⟩ | hxG
    · exact he.symm ▸ h0Q.1
    · exact hE.2.subset hx
    · exact hGQ hxG
  have hMidCover : ∀ x ∈ edgeTrace w L, ∃ k, retract f b o x ∈ F k := by
    intro x hx
    have hyP := retract_mem Q hQ f b o x ho (hMidQ x hx) hs
    rcases retract_eq_self_or_on_cut f b o x hs with he | ⟨i, hi⟩
    · rcases exterior_edgeTrace_cases Q G hG w L hsteps hx with hx0 | ⟨k, hk, hE, hxE⟩ | hxG
      · exact ⟨.inl none, hyP, he.trans hx0⟩
      · refine ⟨.inl (some ⟨k, hk⟩), ?_⟩
        change retract f b o x ∈ if Adj Q (w k) (w (k + 1)) then P ∩ segment ℝ (w k) (w (k + 1)) else ∅
        rw [if_pos hE]
        exact ⟨hyP, he.symm ▸ hxE⟩
      · exact False.elim (hout x hxG (he ▸ hyP))
    · exact ⟨.inr i, hyP, hi⟩
  let K := (segment ℝ u (w 0) ∪ edgeTrace w L) ∪ segment ℝ (w L) v
  have hK : IsPreconnected K :=
    ((convex_segment u (w 0)).isPreconnected.union'
      ⟨w 0, right_mem_segment ℝ _ _, edgeTrace_start w L⟩ (edgeTrace_preconnected w L)).union'
      ⟨w L, Or.inr (edgeTrace_end w L), left_mem_segment ℝ _ _⟩
      (convex_segment (w L) v).isPreconnected
  let T := retract f b o '' K
  have hT : IsPreconnected T := hK.image _ (continuous_retract f b o).continuousOn
  have hCover : ∀ y ∈ T, ∃ k, y ∈ F k := by
    rintro y ⟨x, hx, rfl⟩
    rcases hx with (hx | hx) | hx
    · rcases hAu with he | hAu
      · have hx0 : x = w 0 := by simpa [he] using hx
        exact hMidCover x (hx0.symm ▸ edgeTrace_start w L)
      · obtain ⟨i, hi, he⟩ := hAu x hx
        exact ⟨.inr i, hi, he⟩
    · exact hMidCover x hx
    · rcases hAv with he | hAv
      · have hxL : x = w L := by simpa [he] using hx
        exact hMidCover x (hxL.symm ▸ edgeTrace_end w L)
      · have hx' : x ∈ segment ℝ v (w L) := by rwa [segment_symm]
        obtain ⟨i, hi, he⟩ := hAv x hx'
        exact ⟨.inr i, hi, he⟩
  have huT : u ∈ T :=
    ⟨u, Or.inl (Or.inl (left_mem_segment ℝ _ _)), retract_fixes Q f b o u hs hu.1⟩
  have hvT : v ∈ T :=
    ⟨v, Or.inr (right_mem_segment ℝ _ _), retract_fixes Q f b o v hs hv.1⟩
  have hr := route_of_preconnected_closed_face_cover
    P F C hP hFace hClosed hDiam T hT hCover u v huT hvT hu hv
  simpa [C, Fintype.sum_sum_type, Fintype.sum_option] using hr

/-- Diameter transfer using actual outer edges and convex exterior-cap
shortcuts. New final vertices are lifted by compact optimization, not assumed
already connected. No cap-diameter budget occurs in the conclusion. -/
theorem clip_diameter_from_exterior_routes
    (Q G : Set (ClipSpace d)) (hQ : Convex ℝ Q) (hQc : IsCompact Q)
    (hG : Convex ℝ G) (hGQ : G ⊆ Q)
    (f : ι → ClipSpace d →L[ℝ] ℝ) (b : ι → ℝ)
    (o : ClipSpace d) (ho : o ∈ Q) (hs : ∀ i, f i o < b i)
    (hout : ∀ x ∈ G, x ∉ finalClip Q f b)
    (D : ℕ)
    (hD : ∀ a ∈ extremePoints ℝ Q, ∀ c ∈ extremePoints ℝ Q,
      Route (fun x y => Adj Q x y ∨ (x ∈ G ∧ y ∈ G)) D a c)
    (B : ι → ℕ) (hB : ∀ i, DiamLE (finalClip Q f b ∩ {x | f i x = b i}) (B i)) :
    DiamLE (finalClip Q f b) (D + ∑ i, B i) := by
  have hCuts : IsClosed {x : ClipSpace d | ∀ i, f i x ≤ b i} := by
    simp only [setOf_forall]
    exact isClosed_iInter fun i => isClosed_le (f i).continuous continuous_const
  have hP : IsCompact (finalClip Q f b) := hQc.inter_right hCuts
  intro u hu v hv
  obtain ⟨a, ha, hAu⟩ := final_vertex_attachment Q hQ hQc f b o ho hs u hu
  obtain ⟨c, hc, hAv⟩ := final_vertex_attachment Q hQ hQc f b o ho hs v hv
  obtain ⟨w, hw0, hwD, hwsteps⟩ := hD a ha c hc
  apply clip_route_with_exterior_attachments Q G hQ hG hGQ f b o ho hs hP hout B hB u v hu hv w D
  · simpa only [hw0] using ha
  · exact hwsteps
  · simpa only [hw0] using hAu
  · simpa only [hwD] using hAv

/-- The structural cap condition adds at most ONE step. Both cap endpoints
can be connected directly through the cap, so two ray charges are unnecessary. -/
theorem exterior_cap_augmented_route_bound
    (Q G V : Set (ClipSpace d)) (D : ℕ)
    (hOld : ∀ a ∈ V, ∀ c ∈ V, Route (Adj Q) D a c)
    (hclass : ∀ x ∈ extremePoints ℝ Q,
      x ∈ V ∨ (x ∈ G ∧ ∃ a ∈ V, Adj Q a x)) :
    ∀ u ∈ extremePoints ℝ Q, ∀ v ∈ extremePoints ℝ Q,
      Route (fun x y => Adj Q x y ∨ (x ∈ G ∧ y ∈ G)) (D + 1) u v := by
  let R := fun x y => Adj Q x y ∨ (x ∈ G ∧ y ∈ G)
  have hOldR : ∀ a ∈ V, ∀ c ∈ V, Route R D a c := by
    intro a ha c hc
    obtain ⟨w, h0, hD, hsteps⟩ := hOld a ha c hc
    refine ⟨w, h0, hD, ?_⟩
    intro k hk
    exact (hsteps k hk).imp id Or.inl
  have pad : ∀ {a c : ClipSpace d} {N : ℕ}, N ≤ D + 1 → Route R N a c → Route R (D + 1) a c := by
    intro a c N hle ⟨w, h0, hN, hs⟩
    exact HirschProduct.pad_walk R hle w h0 hN hs
  have cat : ∀ {a c z : ClipSpace d} {M N : ℕ},
      Route R M a c → Route R N c z → Route R (M + N) a z := by
    intro a c z M N ⟨w, h0, hM, hw⟩ ⟨q, hq0, hqN, hq⟩
    exact HirschProduct.append_walk R w q h0 hM hq0 hqN hw hq
  intro u hu v hv
  rcases hclass u hu with huV | ⟨huG, a, haV, hau⟩
  · rcases hclass v hv with hvV | ⟨hvG, c, hcV, hcv⟩
    · exact pad (by omega) (hOldR u huV v hvV)
    · exact cat (hOldR u huV c hcV) (route_one R (Or.inr (Or.inl hcv)))
  · rcases hclass v hv with hvV | ⟨hvG, c, hcV, hcv⟩
    · have hua : Adj Q u a := ⟨hau.1.symm, by simpa [segment_symm] using hau.2⟩
      have hr := cat (route_one R (Or.inr (Or.inl hua))) (hOldR a haV v hvV)
      simpa [Nat.add_comm] using hr
    · exact pad (by omega) (route_one R (Or.inr (Or.inr ⟨huG, hvG⟩)))

/-- End-to-end cap-witness form of pointed unbounded clipping. A sufficiently
far truncation of a pointed polyhedron has exactly this vertex classification:
old vertices route in D steps; every new cap vertex is adjacent to an old one.
The general polyhedral existence of that truncation is NOT proved in this file.
All final-face costs remain explicit. -/
theorem simultaneous_clip_diameter_from_exterior_cap
    (Q G V : Set (ClipSpace d)) (hQ : Convex ℝ Q) (hQc : IsCompact Q)
    (hG : Convex ℝ G) (hGQ : G ⊆ Q)
    (f : ι → ClipSpace d →L[ℝ] ℝ) (b : ι → ℝ)
    (o : ClipSpace d) (ho : o ∈ Q) (hs : ∀ i, f i o < b i)
    (hout : ∀ x ∈ G, x ∉ finalClip Q f b)
    (D : ℕ) (hOld : ∀ a ∈ V, ∀ c ∈ V, Route (Adj Q) D a c)
    (hclass : ∀ x ∈ extremePoints ℝ Q,
      x ∈ V ∨ (x ∈ G ∧ ∃ a ∈ V, Adj Q a x))
    (B : ι → ℕ) (hB : ∀ i, DiamLE (finalClip Q f b ∩ {x | f i x = b i}) (B i)) :
    DiamLE (finalClip Q f b) (D + 1 + ∑ i, B i) := by
  exact clip_diameter_from_exterior_routes Q G hQ hQc hG hGQ f b o ho hs hout
    (D + 1) (exterior_cap_augmented_route_bound Q G V D hOld hclass) B hB


end HirschExterior
end


-- BEGIN Solutions/PolynomialExteriorCapNoStrict.lean

/-! Remove the explicit strict-centre hypothesis from exterior-route and
exterior-cap simultaneous clipping. If no cut is equality on the whole final
polytope, finite convex averaging produces one point strict for every cut. -/

open scoped BigOperators RealInnerProductSpace
open Set Hirsch HirschRadial HirschRegionRoute

noncomputable section
namespace HirschExterior

variable {d : ℕ} {ι : Type*} [Fintype ι]

/-- For finitely many valid linear inequalities on a nonempty convex set,
either one point is strict for every inequality, or one inequality is equality
everywhere on the set. -/
lemma strict_centre_or_universal_final_cut
    (P : Set (ClipSpace d)) (hP : Convex ℝ P) (hne : P.Nonempty)
    (f : ι → ClipSpace d →L[ℝ] ℝ) (b : ι → ℝ)
    (hbound : ∀ i, ∀ x ∈ P, f i x ≤ b i) :
    (∃ o ∈ P, ∀ i, f i o < b i) ∨
      (∃ i, ∀ x ∈ P, f i x = b i) := by
  classical
  by_cases huniv : ∃ i, ∀ x ∈ P, f i x = b i
  · exact Or.inr huniv
  have hpoint : ∀ i, ∃ x ∈ P, f i x < b i := by
    intro i
    by_contra h
    push_neg at h
    apply huniv
    exact ⟨i, fun x hx => le_antisymm (hbound i x hx) (h x hx)⟩
  have hfinite : ∀ s : Finset ι, ∃ o ∈ P, ∀ i ∈ s, f i o < b i := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        obtain ⟨o, ho⟩ := hne
        exact ⟨o, ho, by simp⟩
    | @insert i s hi ih =>
        obtain ⟨o, ho, hs⟩ := ih
        obtain ⟨x, hx, hix⟩ := hpoint i
        refine ⟨(1 / 2 : ℝ) • o + (1 / 2 : ℝ) • x,
          hP ho hx (by norm_num) (by norm_num) (by norm_num), ?_⟩
        intro j hj
        simp only [map_add, map_smul, smul_eq_mul]
        rcases Finset.mem_insert.mp hj with rfl | hj
        · nlinarith [hbound j o ho]
        · nlinarith [hs j hj, hbound j x hx]
  obtain ⟨o, ho, hs⟩ := hfinite Finset.univ
  exact Or.inl ⟨o, ho, fun i => hs i (Finset.mem_univ _)⟩

/-- Remove the strict-centre binder from the generic exterior-route transfer.
If one cut is equality everywhere on the final polytope, that cut face itself
already supplies the required larger diameter budget. -/
theorem clip_diameter_from_exterior_routes_no_strict
    (Q G : Set (ClipSpace d)) (hQ : Convex ℝ Q) (hQc : IsCompact Q)
    (hG : Convex ℝ G) (hGQ : G ⊆ Q)
    (f : ι → ClipSpace d →L[ℝ] ℝ) (b : ι → ℝ)
    (hout : ∀ x ∈ G, x ∉ finalClip Q f b)
    (D : ℕ)
    (hD : ∀ a ∈ extremePoints ℝ Q, ∀ c ∈ extremePoints ℝ Q,
      Route (fun x y => Adj Q x y ∨ (x ∈ G ∧ y ∈ G)) D a c)
    (B : ι → ℕ)
    (hB : ∀ i, DiamLE (finalClip Q f b ∩ {x | f i x = b i}) (B i)) :
    DiamLE (finalClip Q f b) (D + ∑ i, B i) := by
  classical
  let P := finalClip Q f b
  by_cases hne : P.Nonempty
  · rcases strict_centre_or_universal_final_cut P (finalClip_convex Q hQ f b) hne f b
        (fun i x hx => hx.2 i) with ⟨o, ho, hs⟩ | ⟨i, hi⟩
    · exact clip_diameter_from_exterior_routes
        Q G hQ hQc hG hGQ f b o ho.1 hs hout D hD B hB
    · have heq : P ∩ {x | f i x = b i} = P := by
        apply inter_eq_left.mpr
        exact fun z hz => hi z hz
      have hPi : DiamLE P (B i) := by
        have h := hB i
        change DiamLE (P ∩ {x | f i x = b i}) (B i) at h
        rw [heq] at h
        exact h
      have hle : B i ≤ D + ∑ j, B j := by
        have hsum : B i ≤ ∑ j, B j :=
          Finset.single_le_sum (fun j _ => Nat.zero_le (B j)) (Finset.mem_univ i)
        omega
      intro u hu v hv
      obtain ⟨w, hw0, hwB, hwstep⟩ := hPi u hu v hv
      exact HirschProduct.pad_walk (Adj P) hle w hw0 hwB hwstep
  · intro u hu v hv
    exact False.elim (hne ⟨u, hu.1⟩)

/-- Exterior-cap clipping without a separately supplied strict centre.
The exterior cap, old-vertex routing, and cap-vertex classification remain
explicit hypotheses; only strict feasibility of one chosen centre is removed. -/
theorem simultaneous_clip_diameter_from_exterior_cap_no_strict
    (Q G V : Set (ClipSpace d)) (hQ : Convex ℝ Q) (hQc : IsCompact Q)
    (hG : Convex ℝ G) (hGQ : G ⊆ Q)
    (f : ι → ClipSpace d →L[ℝ] ℝ) (b : ι → ℝ)
    (hout : ∀ x ∈ G, x ∉ finalClip Q f b)
    (D : ℕ) (hOld : ∀ a ∈ V, ∀ c ∈ V, Route (Adj Q) D a c)
    (hclass : ∀ x ∈ extremePoints ℝ Q,
      x ∈ V ∨ (x ∈ G ∧ ∃ a ∈ V, Adj Q a x))
    (B : ι → ℕ)
    (hB : ∀ i, DiamLE (finalClip Q f b ∩ {x | f i x = b i}) (B i)) :
    DiamLE (finalClip Q f b) (D + 1 + ∑ i, B i) := by
  exact clip_diameter_from_exterior_routes_no_strict
    Q G hQ hQc hG hGQ f b hout (D + 1)
    (exterior_cap_augmented_route_bound Q G V D hOld hclass) B hB


end HirschExterior
end


-- BEGIN Solutions/PolynomialHpolyExteriorCapTransfer.lean

/-! Concrete exterior-cap transfer for a finite pointed H-polyhedron.

The abstract compact cap, exterior region, old-vertex routes, and cap-vertex
classification required by the generic exterior clipping theorem are all
constructed from the canonical summed-normal cap.  The only cap-level inputs
left are that the chosen level lies above every old H-vertex and strictly above
the final clipped polytope. -/

open scoped BigOperators RealInnerProductSpace
open Set Hirsch HirschRadial HirschRegionRoute

noncomputable section
namespace HirschHpolyCap

variable {d n : ℕ} {ι : Type*} [Fintype ι]

/-- The horizon face of the canonical capped H-polyhedron. -/
def horizonCap
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) (T : ℝ) :
    Set (EuclideanSpace ℝ (Fin d)) :=
  cappedHpoly a b T ∩ {x | ⟪capNormal a, x⟫ = T}

lemma cappedHpoly_convex
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) (T : ℝ) :
    Convex ℝ (cappedHpoly a b T) := by
  intro x hx y hy α β hα hβ hab
  constructor
  · exact hpoly_convex a b hx.1 hy.1 hα hβ hab
  · change ⟪capNormal a, α • x + β • y⟫ ≤ T
    rw [inner_add_right, inner_smul_right, inner_smul_right]
    have hx' : α * ⟪capNormal a, x⟫ ≤ α * T :=
      mul_le_mul_of_nonneg_left hx.2 hα
    have hy' : β * ⟪capNormal a, y⟫ ≤ β * T :=
      mul_le_mul_of_nonneg_left hy.2 hβ
    calc
      α * ⟪capNormal a, x⟫ + β * ⟪capNormal a, y⟫ ≤ α * T + β * T :=
        add_le_add hx' hy'
      _ = (α + β) * T := by ring
      _ = T := by rw [hab, one_mul]

lemma horizonCap_convex
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) (T : ℝ) :
    Convex ℝ (horizonCap a b T) := by
  intro x hx y hy α β hα hβ hab
  constructor
  · exact cappedHpoly_convex a b T hx.1 hy.1 hα hβ hab
  · change ⟪capNormal a, α • x + β • y⟫ = T
    rw [inner_add_right, inner_smul_right, inner_smul_right, hx.2, hy.2]
    calc
      α * T + β * T = (α + β) * T := by ring
      _ = T := by rw [hab, one_mul]

/-- If the final clipped set lies strictly below the cap level, capping the
outer H-polyhedron does not change that final set. -/
lemma finalClip_capped_eq
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (f : ι → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (c : ι → ℝ) (T : ℝ)
    (hFinalBelow : ∀ x ∈ finalClip (Hpoly a b) f c, ⟪capNormal a, x⟫ < T) :
    finalClip (cappedHpoly a b T) f c = finalClip (Hpoly a b) f c := by
  apply Set.Subset.antisymm
  · intro x hx
    exact ⟨hx.1.1, hx.2⟩
  · intro x hx
    exact ⟨⟨hx.1, (hFinalBelow x hx).le⟩, hx.2⟩

/-- A padded old H-polyhedron diameter route survives the cap whenever every
old H-vertex is below the chosen cap level.  Extremality of intermediate edge
endpoints is recovered from `Adj`, rather than assumed separately. -/
lemma old_diameter_routes_survive_cap
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) (T : ℝ)
    (D : ℕ) (hD : DiamLE (Hpoly a b) D)
    (hOldBelow : ∀ x ∈ extremePoints ℝ (Hpoly a b), ⟪capNormal a, x⟫ ≤ T) :
    ∀ u ∈ extremePoints ℝ (Hpoly a b), ∀ v ∈ extremePoints ℝ (Hpoly a b),
      Route (Adj (cappedHpoly a b T)) D u v := by
  intro u hu v hv
  obtain ⟨w, hw0, hwD, hwstep⟩ := hD u hu v hv
  refine ⟨w, hw0, hwD, ?_⟩
  intro k hk
  rcases hwstep k hk with hstay | hedge
  · exact Or.inl hstay
  · right
    have hleft : w k ∈ extremePoints ℝ (Hpoly a b) :=
      HirschPolynomialAccess.adj_left_extreme (Hpoly a b) hedge
    have hright : w (k + 1) ∈ extremePoints ℝ (Hpoly a b) :=
      HirschPolynomialAccess.adj_right_extreme (Hpoly a b) hedge
    exact old_edge_survives_cap a b T hedge
      (hOldBelow (w k) hleft) (hOldBelow (w (k + 1)) hright)

/-- Concrete pointed-H-polyhedron exterior-cap diameter transfer.

`hkernel` is the finite H-representation form of pointedness: the row normals
have no nonzero common kernel direction.  A cap level `T` above every old
H-vertex and strictly above the final clipped set yields a compact canonical
outer cap.  If the old H-vertex graph has padded diameter `D` and final cut
face `i` has diameter at most `B i`, then the final simultaneous clip has
padded diameter at most `D + 1 + Σ_i B i`. -/
theorem simultaneous_clip_diameter_from_finite_hpoly_far_cap
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (f : ι → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (c : ι → ℝ)
    (T : ℝ)
    (hkernel : ∀ r : EuclideanSpace ℝ (Fin d),
      (∀ j, ⟪a j, r⟫ = 0) → r = 0)
    (D : ℕ) (hD : DiamLE (Hpoly a b) D)
    (hOldBelow : ∀ x ∈ extremePoints ℝ (Hpoly a b), ⟪capNormal a, x⟫ ≤ T)
    (hFinalBelow : ∀ x ∈ finalClip (Hpoly a b) f c, ⟪capNormal a, x⟫ < T)
    (B : ι → ℕ)
    (hB : ∀ i, DiamLE (finalClip (Hpoly a b) f c ∩ {x | f i x = c i}) (B i)) :
    DiamLE (finalClip (Hpoly a b) f c) (D + 1 + ∑ i, B i) := by
  let R := cappedHpoly a b T
  let G := horizonCap a b T
  let V := extremePoints ℝ (Hpoly a b)
  have hR : Convex ℝ R := cappedHpoly_convex a b T
  have hRc : IsCompact R := cappedHpoly_isCompact a b T hkernel
  have hG : Convex ℝ G := horizonCap_convex a b T
  have hGR : G ⊆ R := inter_subset_left
  have hEq : finalClip R f c = finalClip (Hpoly a b) f c := by
    exact finalClip_capped_eq a b f c T hFinalBelow
  have hout : ∀ x ∈ G, x ∉ finalClip R f c := by
    intro x hxG hxP
    have hxOrig : x ∈ finalClip (Hpoly a b) f c := by
      rw [← hEq]
      exact hxP
    exact (ne_of_lt (hFinalBelow x hxOrig)) hxG.2
  have hOld : ∀ u ∈ V, ∀ v ∈ V, Route (Adj R) D u v := by
    exact old_diameter_routes_survive_cap a b T D hD hOldBelow
  have hclass : ∀ x ∈ extremePoints ℝ R,
      x ∈ V ∨ (x ∈ G ∧ ∃ y ∈ V, Adj R y x) := by
    intro x hx
    rcases cap_vertex_old_or_horizon_adjacent a b T x hx with hold | ⟨hhorizon, y, hy, hadj⟩
    · exact Or.inl hold
    · exact Or.inr ⟨⟨hx.1, hhorizon⟩, y, hy, hadj⟩
  have hB' : ∀ i, DiamLE (finalClip R f c ∩ {x | f i x = c i}) (B i) := by
    intro i
    rw [hEq]
    exact hB i
  have hres := HirschExterior.simultaneous_clip_diameter_from_exterior_cap_no_strict
    R G V hR hRc hG hGR f c hout D hOld hclass B hB'
  rw [hEq] at hres
  exact hres


end HirschHpolyCap
end


-- BEGIN Solutions/Sol_Hirsch_finite_hpoly_far_cap_diameter.lean

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

/-- Public-type wrapper for the canonical far-cap transfer on a finite
H-polyhedron.  The summed cap normal and simultaneous clip are expanded in the
statement so the theorem type uses only Mathlib and the public Hirsch model. -/
theorem solution
    {d n : ℕ} {ι : Type*} [Fintype ι]
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (f : ι → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (c : ι → ℝ)
    (T : ℝ)
    (hkernel : ∀ r : EuclideanSpace ℝ (Fin d),
      (∀ j, ⟪a j, r⟫ = 0) → r = 0)
    (D : ℕ) (hD : DiamLE (Hpoly a b) D)
    (hOldBelow : ∀ x ∈ extremePoints ℝ (Hpoly a b),
      ⟪-(∑ j, a j), x⟫ ≤ T)
    (hFinalBelow : ∀ x ∈ Hpoly a b ∩ {y | ∀ i, f i y ≤ c i},
      ⟪-(∑ j, a j), x⟫ < T)
    (B : ι → ℕ)
    (hB : ∀ i, DiamLE
      ((Hpoly a b ∩ {y | ∀ j, f j y ≤ c j}) ∩ {x | f i x = c i}) (B i)) :
    DiamLE (Hpoly a b ∩ {y | ∀ i, f i y ≤ c i}) (D + 1 + ∑ i, B i) := by
  have hOld : ∀ x ∈ extremePoints ℝ (Hpoly a b),
      ⟪HirschHpolyCap.capNormal a, x⟫ ≤ T := by
    simpa [HirschHpolyCap.capNormal] using hOldBelow
  have hFinal : ∀ x ∈ HirschRadial.finalClip (Hpoly a b) f c,
      ⟪HirschHpolyCap.capNormal a, x⟫ < T := by
    simpa [HirschRadial.finalClip, HirschHpolyCap.capNormal] using hFinalBelow
  have hFaces : ∀ i, DiamLE
      (HirschRadial.finalClip (Hpoly a b) f c ∩ {x | f i x = c i}) (B i) := by
    intro i
    simpa [HirschRadial.finalClip] using hB i
  have h := HirschHpolyCap.simultaneous_clip_diameter_from_finite_hpoly_far_cap
    a b f c T hkernel D hD hOld hFinal B hFaces
  simpa [HirschRadial.finalClip] using h


#print axioms solution
