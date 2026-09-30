-- Prove2me | solution 1 for Hirsch.given_supporting_face_access_of_boundary_product_factors
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-06T21:03:32.512516+00:00
-- url     : https://prove2.me/submissions/f888ce43-7c33-4db4-9eb6-aba58264db73

import Definitions.Def_Hirsch_model
import Mathlib
import Theorems.Thm_Hirsch_larman_bound

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


-- BEGIN Solutions/PolynomialAffineProductFace.lean

open Set Hirsch

set_option maxHeartbeats 4000000

noncomputable section

namespace HirschProduct

variable {E F : Type*} [AddCommGroup E] [Module ℝ E]
  [AddCommGroup F] [Module ℝ F]

/-- Pull an ambient extreme point back through an injective affine face chart. -/
lemma extreme_preimage (f : E →ᵃ[ℝ] F) (hinj : Function.Injective f)
    (Q : Set E) (P : Set F) (hsub : f '' Q ⊆ P)
    {q : E} (hq : q ∈ Q) (hext : f q ∈ extremePoints ℝ P) :
    q ∈ extremePoints ℝ Q := by
  refine ⟨hq, ?_⟩
  intro p hp r hr hop
  have hmap : f q ∈ openSegment ℝ (f p) (f r) := by
    rw [← image_openSegment ℝ f p r]
    exact ⟨q, hop, rfl⟩
  exact hinj (hext.2 (hsub ⟨p, hp, rfl⟩) (hsub ⟨r, hr, rfl⟩) hmap)

/-- Injective affine maps preserve edges of a set onto its affine image. -/
lemma adj_affine_image (f : E →ᵃ[ℝ] F) (hinj : Function.Injective f)
    (Q : Set E) {p q : E} (hadj : Adj Q p q) :
    Adj (f '' Q) (f p) (f q) := by
  refine ⟨fun h => hadj.1 (hinj h), ?_, ?_⟩
  · intro z hz
    rw [← image_segment ℝ f p q] at hz
    obtain ⟨t, ht, rfl⟩ := hz
    exact ⟨t, hadj.2.subset ht, rfl⟩
  · intro x hx y hy z hz hop
    obtain ⟨x', hx', rfl⟩ := hx
    obtain ⟨y', hy', rfl⟩ := hy
    rw [← image_segment ℝ f p q] at hz
    obtain ⟨z', hz', rfl⟩ := hz
    rw [← image_openSegment ℝ f x' y'] at hop
    obtain ⟨t, ht, htz⟩ := hop
    have heq : t = z' := hinj htz
    subst t
    rw [← image_segment ℝ f p q]
    exact ⟨x', hadj.2.left_mem_of_mem_openSegment hx' hy' hz' ht, rfl⟩

/-- A walk in an affine product face gives a parent-polytope walk with exactly
the same budget. The chart need not be orthogonal; shears are allowed. -/
lemma walk_via_affine_face
    (P : Set F) (Q : Set E) (f : E →ᵃ[ℝ] F)
    (hinj : Function.Injective f) (hface : IsExtreme ℝ P (f '' Q))
    (u x : F) (hu : u ∈ extremePoints ℝ P) (hx : x ∈ extremePoints ℝ P)
    (hui : u ∈ f '' Q) (hxi : x ∈ f '' Q)
    (B : ℕ) (hD : DiamLE Q B) :
    ∃ w : ℕ → F, w 0 = u ∧ w B = x ∧
      ∀ j < B, w j = w (j + 1) ∨ Adj P (w j) (w (j + 1)) := by
  obtain ⟨qu, hqu, hfu⟩ := hui
  obtain ⟨qx, hqx, hfx⟩ := hxi
  have heu : qu ∈ extremePoints ℝ Q :=
    extreme_preimage f hinj Q P hface.subset hqu (by simpa only [hfu] using hu)
  have hex : qx ∈ extremePoints ℝ Q :=
    extreme_preimage f hinj Q P hface.subset hqx (by simpa only [hfx] using hx)
  obtain ⟨wq, hw0, hwB, hws⟩ := hD qu heu qx hex
  refine ⟨fun j => f (wq j), ?_, ?_, ?_⟩
  · exact (congrArg f hw0).trans hfu
  · exact (congrArg f hwB).trans hfx
  · intro j hj
    rcases hws j hj with h | h
    · exact Or.inl (congrArg f h)
    · have hi := adj_affine_image f hinj Q h
      exact Or.inr ⟨hi.1, hface.trans hi.2⟩


end HirschProduct
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


-- BEGIN Solutions/PolynomialBoundaryWalk.lean

open Set Hirsch

set_option maxHeartbeats 3000000

noncomputable section

namespace HirschProduct

/-- A first target contact in a padded walk crosses a genuine edge. -/
lemma first_contact {E : Type*} (R : E → E → Prop) (T : E → Prop)
    {D : ℕ} (w : ℕ → E)
    (h0 : ¬ T (w 0)) (hD : T (w D))
    (hs : ∀ j < D, w j = w (j + 1) ∨ R (w j) (w (j + 1))) :
    ∃ j < D, ¬ T (w j) ∧ T (w (j + 1)) ∧ R (w j) (w (j + 1)) := by
  classical
  have hex : ∃ k : ℕ, k ≤ D ∧ T (w k) := ⟨D, le_rfl, hD⟩
  let k := Nat.find hex
  have hk : k ≤ D ∧ T (w k) := Nat.find_spec hex
  have hk0 : k ≠ 0 := by
    intro h
    apply h0
    simpa only [h] using hk.2
  obtain ⟨j, hjk⟩ := Nat.exists_eq_succ_of_ne_zero hk0
  have hjD : j < D := by omega
  have hjnot : ¬ T (w j) := by
    intro hjT
    have hmin : k ≤ j := Nat.find_min' hex ⟨by omega, hjT⟩
    omega
  have hjnext : T (w (j + 1)) := by simpa only [hjk, Nat.succ_eq_add_one] using hk.2
  have hadj : R (w j) (w (j + 1)) := by
    rcases hs j hjD with heq | hadj
    · exact False.elim (hjnot (heq ▸ hjnext))
    · exact hadj
  exact ⟨j, hjD, hjnot, hjnext, hadj⟩

/-- Short prefixes to the predecessors of target-crossing edges are enough.
No low-dimension assumption is built into this graph/face interface. -/
theorem access_of_boundary_walks {d : ℕ}
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (u v : EuclideanSpace ℝ (Fin d)) (hu : u ∈ extremePoints ℝ P)
    (T : EuclideanSpace ℝ (Fin d) → Prop) (hTv : T v)
    (B : ℕ)
    (hconn : ∃ D : ℕ, ∃ w : ℕ → EuclideanSpace ℝ (Fin d),
      w 0 = u ∧ w D = v ∧
      ∀ j < D, w j = w (j + 1) ∨ Adj P (w j) (w (j + 1)))
    (hshort : ∀ x z, Adj P x z → ¬ T x → T z →
      ∃ w : ℕ → EuclideanSpace ℝ (Fin d),
        w 0 = u ∧ w B = x ∧
        ∀ j < B, w j = w (j + 1) ∨ Adj P (w j) (w (j + 1))) :
    ∃ z : EuclideanSpace ℝ (Fin d), z ∈ extremePoints ℝ P ∧ T z ∧
      ∃ w : ℕ → EuclideanSpace ℝ (Fin d),
        w 0 = u ∧ w (B + 1) = z ∧
        ∀ j < B + 1, w j = w (j + 1) ∨ Adj P (w j) (w (j + 1)) := by
  classical
  by_cases hTu : T u
  · exact ⟨u, hu, hTu, fun _ => u, rfl, rfl, fun _ _ => Or.inl rfl⟩
  obtain ⟨D, w, hw0, hwD, hws⟩ := hconn
  obtain ⟨j, hjD, hx, hz, hadj⟩ := first_contact (Adj P) T w
    (by simpa only [hw0] using hTu) (by simpa only [hwD] using hTv) hws
  have hzext := HirschPolynomialAccess.adj_right_extreme P hadj
  obtain ⟨p, hp0, hpB, hps⟩ := hshort (w j) (w (j + 1)) hadj hx hz
  let q : ℕ → EuclideanSpace ℝ (Fin d) := fun k => if k = 0 then w j else w (j + 1)
  have hq0 : q 0 = w j := by simp only [q, if_pos rfl]
  have hq1 : q 1 = w (j + 1) := by simp [q]
  have hqs : ∀ k < 1, q k = q (k + 1) ∨ Adj P (q k) (q (k + 1)) := by
    intro k hk
    have hk0 : k = 0 := by omega
    subst k
    exact Or.inr (by simpa only [Nat.zero_add, hq0, hq1] using hadj)
  obtain ⟨wp, hp0, hpB, hps⟩ := append_walk (Adj P) p q hp0 hpB hq0 hq1 hps hqs
  exact ⟨w (j + 1), hzext, hz, wp, hp0, hpB, hps⟩


end HirschProduct
end


-- BEGIN Solutions/PolynomialBoundaryProductSubmission.lean

open scoped RealInnerProductSpace
open Set Hirsch HirschProduct

set_option maxHeartbeats 5000000

noncomputable section

/-- Prescribed supporting-face access via affine product faces.
For every edge entering the fixed row i, its outside endpoint and u must lie
in an affine product face. Factor dimensions are bounded by r, and the TOTAL
number of factor describing rows is at most M. Total dimension and total
residual rank may be arbitrarily large. This is a structural restriction,
not an assertion that every polytope has such product faces. -/
theorem solution
    (d n M r : ℕ)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hbd : Bornology.IsBounded (Hpoly a b))
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hv : v ∈ extremePoints ℝ (Hpoly a b))
    (i : Fin n) (hiv : ⟪a i, v⟫ = b i)
    (hfactor : ∀ x z, Adj (Hpoly a b) x z →
      ⟪a i, x⟫ ≠ b i → ⟪a i, z⟫ = b i →
      ∃ (m : ℕ) (ds ns : Fin m → ℕ)
        (aa : (k : Fin m) → Fin (ns k) → EuclideanSpace ℝ (Fin (ds k)))
        (bb : (k : Fin m) → Fin (ns k) → ℝ)
        (f : ((k : Fin m) → EuclideanSpace ℝ (Fin (ds k))) →ᵃ[ℝ]
          EuclideanSpace ℝ (Fin d)),
        Function.Injective f ∧
        IsExtreme ℝ (Hpoly a b) (f '' Set.univ.pi (fun k => Hpoly (aa k) (bb k))) ∧
        u ∈ f '' Set.univ.pi (fun k => Hpoly (aa k) (bb k)) ∧
        x ∈ f '' Set.univ.pi (fun k => Hpoly (aa k) (bb k)) ∧
        (∀ k, Bornology.IsBounded (Hpoly (aa k) (bb k))) ∧
        (∀ k, ds k ≤ r) ∧ (∑ k, ns k) ≤ M) :
    ∃ z : EuclideanSpace ℝ (Fin d),
      z ∈ extremePoints ℝ (Hpoly a b) ∧ ⟪a i, z⟫ = b i ∧
      ∃ w : ℕ → EuclideanSpace ℝ (Fin d),
        w 0 = u ∧ w (M * 2 ^ (r - 3) + 1) = z ∧
        ∀ j < M * 2 ^ (r - 3) + 1,
          w j = w (j + 1) ∨ Adj (Hpoly a b) (w j) (w (j + 1)) := by
  classical
  let B : ℕ := M * 2 ^ (r - 3)
  have hconn : ∃ D : ℕ, ∃ w : ℕ → EuclideanSpace ℝ (Fin d),
      w 0 = u ∧ w D = v ∧
      ∀ j < D, w j = w (j + 1) ∨ Adj (Hpoly a b) (w j) (w (j + 1)) := by
    obtain ⟨w, hw0, hwD, hws⟩ :=
      Hirsch.larman_bound d n a b ⟨u, hu.1⟩ hbd u hu v hv
    exact ⟨n * 2 ^ (d - 3), w, hw0, hwD, hws⟩
  apply access_of_boundary_walks (Hpoly a b) u v hu
    (fun y => ⟪a i, y⟫ = b i) hiv B hconn
  intro x z hxz hxi hzi
  obtain ⟨m, ds, ns, aa, bb, f, hinj, hface, hui, hxi', hbounded, hdim, hrows⟩ :=
    hfactor x z hxz hxi hzi
  let Q : Set ((k : Fin m) → EuclideanSpace ℝ (Fin (ds k))) :=
    Set.univ.pi (fun k => Hpoly (aa k) (bb k))
  have hQne : Q.Nonempty := by
    obtain ⟨q, hq, _⟩ := hui
    exact ⟨q, hq⟩
  have hne (k : Fin m) : (Hpoly (aa k) (bb k)).Nonempty :=
    ⟨hQne.choose k, (Set.mem_univ_pi.mp hQne.choose_spec) k⟩
  let L : ℕ := ∑ k, ns k * 2 ^ (ds k - 3)
  have hDQ : DiamLE Q L :=
    diamLE_pi (fun k => Hpoly (aa k) (bb k))
      (fun k => ns k * 2 ^ (ds k - 3))
      (fun k => Hirsch.larman_bound (ds k) (ns k) (aa k) (bb k) (hne k) (hbounded k))
  have hLB : L ≤ B := by
    calc
      L ≤ ∑ k, ns k * 2 ^ (r - 3) := by
        apply Finset.sum_le_sum
        intro k _
        exact Nat.mul_le_mul_left (ns k)
          (Nat.pow_le_pow_right (by omega) (Nat.sub_le_sub_right (hdim k) 3))
      _ = (∑ k, ns k) * 2 ^ (r - 3) := by rw [Finset.sum_mul]
      _ ≤ B := Nat.mul_le_mul_right (2 ^ (r - 3)) hrows
  have hxext := HirschPolynomialAccess.adj_left_extreme (Hpoly a b) hxz
  obtain ⟨w, hw0, hwL, hws⟩ :=
    walk_via_affine_face (Hpoly a b) Q f hinj hface u x hu hxext hui hxi' L hDQ
  exact HirschProduct.pad_walk (Adj (Hpoly a b)) hLB w hw0 hwL hws

end


#print axioms solution
