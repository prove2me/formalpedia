-- Prove2me | solution 1 for Hirsch.geodesic_face_disjoint_tail_bound
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-09T02:13:29.75128+00:00
-- url     : https://prove2.me/submissions/3237871f-7670-4489-8e96-340312b9792a

import Mathlib
import Definitions.Def_Hirsch_model

set_option maxHeartbeats 8000000
noncomputable section

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

open scoped RealInnerProductSpace BigOperators
open Set Hirsch

set_option maxHeartbeats 5000000

noncomputable section

attribute [local instance] Classical.propDecidable

namespace HirschFaceSplice

abbrev Walk {d : ℕ} (P : Set (EuclideanSpace ℝ (Fin d)))
    (L : ℕ) (u v : EuclideanSpace ℝ (Fin d)) : Prop :=
  ∃ w : ℕ → EuclideanSpace ℝ (Fin d), w 0 = u ∧ w L = v ∧
    ∀ j < L, w j = w (j + 1) ∨ Adj P (w j) (w (j + 1))

/-- Minimum length among the finite padded graph walks with fixed endpoints.
This is not a non-revisiting-face hypothesis. -/
def IsShortestLength {d : ℕ} (P : Set (EuclideanSpace ℝ (Fin d)))
    (u v : EuclideanSpace ℝ (Fin d)) (L : ℕ) : Prop :=
  ∀ K : ℕ, Walk P K u v → L ≤ K

lemma walk_vertices_extreme {d L : ℕ}
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (w : ℕ → EuclideanSpace ℝ (Fin d))
    (h0 : w 0 ∈ extremePoints ℝ P)
    (hs : ∀ j < L, w j = w (j + 1) ∨ Adj P (w j) (w (j + 1))) :
    ∀ j ≤ L, w j ∈ extremePoints ℝ P := by
  intro j
  induction j with
  | zero => intro _; exact h0
  | succ j ih =>
    intro hj
    have hjL : j < L := by omega
    rcases hs j hjL with heq | hadj
    · rw [← heq]
      exact ih (by omega)
    · exact HirschPolynomialAccess.adj_right_extreme P hadj

/-- First and last visits to a face on a shortest parent path are at most
its intrinsic graph diameter apart. No face-convexity of shortest paths is
assumed: this follows by replacing the entire intervening subpath. -/
theorem shortest_face_visit_span_le
    (d L B s t : ℕ)
    (P F : Set (EuclideanSpace ℝ (Fin d)))
    (hF : IsExtreme ℝ P F) (hFD : DiamLE F B)
    (u v : EuclideanSpace ℝ (Fin d))
    (w : ℕ → EuclideanSpace ℝ (Fin d))
    (hw0 : w 0 = u) (hwL : w L = v)
    (hs : ∀ j < L, w j = w (j + 1) ∨ Adj P (w j) (w (j + 1)))
    (hmin : IsShortestLength P u v L)
    (hst : s ≤ t) (htL : t ≤ L)
    (hsP : w s ∈ extremePoints ℝ P) (htP : w t ∈ extremePoints ℝ P)
    (hsF : w s ∈ F) (htF : w t ∈ F) :
    t - s ≤ B := by
  have hw' := splice_reentry_through_extreme_face
    d L B s t P F hF hFD u v w hw0 hwL hs hst htL hsP htP hsF htF
  have hle := hmin (s + B + (L - t)) hw'
  omega

/-- Count visits, rather than excursions. The bound includes both endpoints
of the path. It is valid even when the path leaves and re-enters the face. -/
theorem shortest_face_visit_card_le
    (d L B : ℕ)
    (P F : Set (EuclideanSpace ℝ (Fin d)))
    (hF : IsExtreme ℝ P F) (hFD : DiamLE F B)
    (u v : EuclideanSpace ℝ (Fin d))
    (w : ℕ → EuclideanSpace ℝ (Fin d))
    (hw0 : w 0 = u) (hwL : w L = v)
    (hs : ∀ j < L, w j = w (j + 1) ∨ Adj P (w j) (w (j + 1)))
    (hmin : IsShortestLength P u v L)
    (hverts : ∀ j ≤ L, w j ∈ extremePoints ℝ P) :
    ((Finset.range (L + 1)).filter (fun j => w j ∈ F)).card ≤ B + 1 := by
  classical
  let S := (Finset.range (L + 1)).filter (fun j => w j ∈ F)
  change S.card ≤ B + 1
  by_cases hne : S.Nonempty
  · let s := S.min' hne
    have hsS : s ∈ S := Finset.min'_mem S hne
    have hsL : s ≤ L := by
      have := Finset.mem_range.mp (Finset.mem_filter.mp hsS).1
      omega
    have hsF : w s ∈ F := (Finset.mem_filter.mp hsS).2
    have hsub : S ⊆ Finset.Icc s (s + B) := by
      intro t ht
      have hst : s ≤ t := Finset.min'_le S t ht
      have htL : t ≤ L := by
        have := Finset.mem_range.mp (Finset.mem_filter.mp ht).1
        omega
      have htF : w t ∈ F := (Finset.mem_filter.mp ht).2
      have hspan := shortest_face_visit_span_le d L B s t P F hF hFD u v
        w hw0 hwL hs hmin hst htL (hverts s hsL) (hverts t htL) hsF htF
      exact Finset.mem_Icc.mpr ⟨hst, by omega⟩
    have hcard : (Finset.Icc s (s + B)).card = B + 1 := by simp [Nat.add_assoc]
    exact (Finset.card_le_card hsub).trans_eq hcard
  · have hS : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    simp [hS]

/-- Double-count incidences between vertices of a shortest path and a finite
family of extreme faces. Each path vertex must be covered at least `q`
times; each face is charged at most its intrinsic diameter plus one.

This is a proved geometric certificate, not an assertion that a cheap cover
exists for every polytope. -/
theorem shortest_face_cover_budget
    {ι : Type*} [Fintype ι]
    (d L q : ℕ)
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (F : ι → Set (EuclideanSpace ℝ (Fin d))) (B : ι → ℕ)
    (hF : ∀ i, IsExtreme ℝ P (F i)) (hFD : ∀ i, DiamLE (F i) (B i))
    (u v : EuclideanSpace ℝ (Fin d))
    (w : ℕ → EuclideanSpace ℝ (Fin d))
    (hw0 : w 0 = u) (hwL : w L = v)
    (hs : ∀ j < L, w j = w (j + 1) ∨ Adj P (w j) (w (j + 1)))
    (hmin : IsShortestLength P u v L)
    (hverts : ∀ j ≤ L, w j ∈ extremePoints ℝ P)
    (hcover : ∀ j ≤ L, q ≤ (Finset.univ.filter (fun i => w j ∈ F i)).card) :
    q * (L + 1) ≤ ∑ i, (B i + 1) := by
  classical
  have hcount :
      (∑ j ∈ Finset.range (L + 1),
        (Finset.univ.filter (fun i => w j ∈ F i)).card) =
      ∑ i, ((Finset.range (L + 1)).filter (fun j => w j ∈ F i)).card := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    exact Finset.sum_comm
  calc
    q * (L + 1) = ∑ _j ∈ Finset.range (L + 1), q := by simp [Nat.mul_comm]
    _ ≤ ∑ j ∈ Finset.range (L + 1),
        (Finset.univ.filter (fun i => w j ∈ F i)).card := by
      apply Finset.sum_le_sum
      intro j hj
      exact hcover j (by have := Finset.mem_range.mp hj; omega)
    _ = ∑ i, ((Finset.range (L + 1)).filter (fun j => w j ∈ F i)).card := hcount
    _ ≤ ∑ i, (B i + 1) := by
      apply Finset.sum_le_sum
      intro i _
      exact shortest_face_visit_card_le d L (B i) P (F i) (hF i) (hFD i)
        u v w hw0 hwL hs hmin hverts

/-- Connectivity alone supplies a shortest path. A multiplicity-q face cover
then gives the explicit parent graph diameter budget
`(sum_i (B_i+1))/q - 1`.

In particular no numerical diameter bound for the parent is assumed. -/
theorem diamLE_of_face_cover
    {ι : Type*} [Fintype ι]
    (d q : ℕ) (hq : 0 < q)
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (F : ι → Set (EuclideanSpace ℝ (Fin d))) (B : ι → ℕ)
    (hF : ∀ i, IsExtreme ℝ P (F i)) (hFD : ∀ i, DiamLE (F i) (B i))
    (hcover : ∀ x ∈ extremePoints ℝ P,
      q ≤ (Finset.univ.filter (fun i => x ∈ F i)).card)
    (hconnect : ∀ u ∈ extremePoints ℝ P, ∀ v ∈ extremePoints ℝ P,
      ∃ L, Walk P L u v) :
    DiamLE P ((∑ i, (B i + 1)) / q - 1) := by
  classical
  intro u hu v hv
  have hex : ∃ L, Walk P L u v := hconnect u hu v hv
  let L := Nat.find hex
  obtain ⟨w, hw0, hwL, hs⟩ := Nat.find_spec hex
  have hmin : IsShortestLength P u v L := by
    intro K hK
    exact Nat.find_min' hex hK
  have hverts : ∀ j ≤ L, w j ∈ extremePoints ℝ P :=
    walk_vertices_extreme P w (by simpa only [hw0] using hu) hs
  have hbudget := shortest_face_cover_budget d L q P F B hF hFD u v
    w hw0 hwL hs hmin hverts (fun j hj => hcover (w j) (hverts j hj))
  have hquot : L + 1 ≤ (∑ i, (B i + 1)) / q := by
    apply (Nat.le_div_iff_mul_le hq).mpr
    simpa only [Nat.mul_comm] using hbudget
  have hL : L ≤ (∑ i, (B i + 1)) / q - 1 := by omega
  exact HirschProduct.pad_walk (Adj P) hL w hw0 hwL hs


end HirschFaceSplice

open scoped RealInnerProductSpace
open Set Hirsch

set_option maxHeartbeats 5000000

noncomputable section

namespace HirschFaceSplice

/-- A shortest walk cannot repeat a vertex. The singleton face at the
repeated vertex has diameter zero, so the face-span lemma applies. -/
lemma shortest_no_repeat_of_le
    (d L s t : ℕ) (P : Set (EuclideanSpace ℝ (Fin d)))
    (u v : EuclideanSpace ℝ (Fin d))
    (w : ℕ → EuclideanSpace ℝ (Fin d))
    (hw0 : w 0 = u) (hwL : w L = v)
    (hs : ∀ j < L, w j = w (j + 1) ∨ Adj P (w j) (w (j + 1)))
    (hmin : IsShortestLength P u v L)
    (hverts : ∀ j ≤ L, w j ∈ extremePoints ℝ P)
    (hst : s ≤ t) (htL : t ≤ L) (heq : w s = w t) : s = t := by
  have hsL : s ≤ L := hst.trans htL
  have hsext := hverts s hsL
  have hsingle : IsExtreme ℝ P ({w s} : Set (EuclideanSpace ℝ (Fin d))) := by
    refine ⟨?_, ?_⟩
    · intro y hy
      have hy' : y = w s := Set.mem_singleton_iff.mp hy
      rw [hy']
      exact hsext.1
    · intro p hp q hq z hz hseg
      have hz' : z = w s := Set.mem_singleton_iff.mp hz
      rw [hz'] at hseg
      exact Set.mem_singleton_iff.mpr (hsext.2 hp hq hseg)
  have hD : DiamLE ({w s} : Set (EuclideanSpace ℝ (Fin d))) 0 := by
    intro p hp q hq
    have hp' : p = w s := Set.mem_singleton_iff.mp hp.1
    have hq' : q = w s := Set.mem_singleton_iff.mp hq.1
    refine ⟨fun _ => p, rfl, hp'.trans hq'.symm, ?_⟩
    intro j hj
    omega
  have hspan := shortest_face_visit_span_le d L 0 s t P {w s}
    hsingle hD u v w hw0 hwL hs hmin hst htL hsext (hverts t htL)
    (by simp) (by simpa only [Set.mem_singleton_iff] using heq.symm)
  omega

/-- After position B, a shortest path can only visit vertices sharing no
selected face with its start. An explicit finite set T containing those
vertices therefore bounds the entire tail, not just its incidence count. -/
theorem shortest_face_disjoint_tail_budget
    {ι : Type*} (d L B : ℕ)
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (F : ι → Set (EuclideanSpace ℝ (Fin d)))
    (hF : ∀ i, IsExtreme ℝ P (F i)) (hFD : ∀ i, DiamLE (F i) B)
    (u v : EuclideanSpace ℝ (Fin d))
    (w : ℕ → EuclideanSpace ℝ (Fin d))
    (hw0 : w 0 = u) (hwL : w L = v)
    (hs : ∀ j < L, w j = w (j + 1) ∨ Adj P (w j) (w (j + 1)))
    (hmin : IsShortestLength P u v L)
    (hverts : ∀ j ≤ L, w j ∈ extremePoints ℝ P)
    (T : Finset (EuclideanSpace ℝ (Fin d)))
    (htail : ∀ x ∈ extremePoints ℝ P,
      (∀ i, u ∈ F i → x ∉ F i) → x ∈ T) : L ≤ B + T.card := by
  classical
  let I := Finset.Icc (B + 1) L
  have hsub : I.image w ⊆ T := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
    have hjI : B + 1 ≤ j ∧ j ≤ L := Finset.mem_Icc.mp hj
    apply htail (w j) (hverts j hjI.2)
    intro i hui hji
    have hspan := shortest_face_visit_span_le d L B 0 j P (F i)
      (hF i) (hFD i) u v w hw0 hwL hs hmin (Nat.zero_le j) hjI.2
      (hverts 0 (Nat.zero_le L)) (hverts j hjI.2)
      (by simpa only [hw0] using hui) hji
    omega
  have hinj : Set.InjOn w I := by
    intro s hsI t htI heq
    have hsL : s ≤ L := (Finset.mem_Icc.mp hsI).2
    have htL : t ≤ L := (Finset.mem_Icc.mp htI).2
    by_cases hst : s ≤ t
    · exact shortest_no_repeat_of_le d L s t P u v w hw0 hwL hs hmin hverts
        hst htL heq
    · exact (shortest_no_repeat_of_le d L t s P u v w hw0 hwL hs hmin hverts
        (by omega) hsL heq.symm).symm
  have hcount : I.card ≤ T.card := by
    calc
      I.card = (I.image w).card := (Finset.card_image_iff.mpr hinj).symm
      _ ≤ T.card := Finset.card_le_card hsub
  have hIcard : I.card = L - B := by simp [I]
  rw [hIcard] at hcount
  omega

/-- A uniform B bound for selected face diameters and at most K vertices
sharing no selected face with any start give parent diameter at most B+K.
The face family need not be finite, and no parent diameter is assumed. -/
theorem diamLE_of_disjoint_face_tail_bound
    {ι : Type*} (d B K : ℕ)
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (F : ι → Set (EuclideanSpace ℝ (Fin d)))
    (hF : ∀ i, IsExtreme ℝ P (F i)) (hFD : ∀ i, DiamLE (F i) B)
    (htails : ∀ u ∈ extremePoints ℝ P,
      ∃ T : Finset (EuclideanSpace ℝ (Fin d)), T.card ≤ K ∧
        ∀ x ∈ extremePoints ℝ P, (∀ i, u ∈ F i → x ∉ F i) → x ∈ T)
    (hconnect : ∀ u ∈ extremePoints ℝ P, ∀ v ∈ extremePoints ℝ P,
      ∃ L, Walk P L u v) : DiamLE P (B + K) := by
  classical
  intro u hu v hv
  obtain ⟨T, hTcard, hT⟩ := htails u hu
  have hex : ∃ L, Walk P L u v := hconnect u hu v hv
  let L := Nat.find hex
  obtain ⟨w, hw0, hwL, hs⟩ := Nat.find_spec hex
  have hmin : IsShortestLength P u v L := by
    intro A hA
    exact Nat.find_min' hex hA
  have hverts : ∀ j ≤ L, w j ∈ extremePoints ℝ P :=
    walk_vertices_extreme P w (by simpa only [hw0] using hu) hs
  have hbound := shortest_face_disjoint_tail_budget d L B P F hF hFD
    u v w hw0 hwL hs hmin hverts T hT
  have hLK : L ≤ B + K := hbound.trans (Nat.add_le_add_left hTcard B)
  exact HirschProduct.pad_walk (Adj P) hLK w hw0 hwL hs


end HirschFaceSplice


open scoped RealInnerProductSpace
open Set Hirsch

theorem solution
    {ι : Type*} (d B K : ℕ)
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (F : ι → Set (EuclideanSpace ℝ (Fin d)))
    (hF : ∀ i, IsExtreme ℝ P (F i)) (hFD : ∀ i, DiamLE (F i) B)
    (htails : ∀ u ∈ extremePoints ℝ P,
      ∃ T : Finset (EuclideanSpace ℝ (Fin d)), T.card ≤ K ∧
        ∀ x ∈ extremePoints ℝ P, (∀ i, u ∈ F i → x ∉ F i) → x ∈ T)
    (hconnect : ∀ u ∈ extremePoints ℝ P, ∀ v ∈ extremePoints ℝ P,
      ∃ L : ℕ, ∃ w : ℕ → EuclideanSpace ℝ (Fin d),
        w 0 = u ∧ w L = v ∧
        ∀ j < L, w j = w (j + 1) ∨ Adj P (w j) (w (j + 1))) :
    DiamLE P (B + K) := by
  apply HirschFaceSplice.diamLE_of_disjoint_face_tail_bound
    d B K P F hF hFD htails
  intro u hu v hv
  obtain ⟨L, w, h0, hL, hs⟩ := hconnect u hu v hv
  exact ⟨L, w, h0, hL, hs⟩

#print axioms solution
