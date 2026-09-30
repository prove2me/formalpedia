-- Prove2me | solution 1 for Hirsch.simultaneous_clipping_diameter_bound
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-10T03:55:48.851465+00:00
-- url     : https://prove2.me/submissions/0dd040a3-3e38-4d48-9f54-bb07df0fa5a1

import Definitions.Def_Hirsch_model
import Mathlib
import Mathlib.Analysis.Convex.KreinMilman

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


-- BEGIN Solutions/PolynomialClosedFaceTrace.lean

/-! Finite closed-cover connectivity for continuous repair traces.
Verification status is recorded in research/ClippingVerificationProgress.md. -/

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

noncomputable section

namespace HirschRegionRoute

lemma finite_closed_region_union {V ι : Type*} [TopologicalSpace V]
    (S : ι → Set V) (hclosed : ∀ i, IsClosed (S i)) (s : Finset ι) :
    IsClosed (⋃ i ∈ s, S i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (isClosed_empty : IsClosed (∅ : Set V))
  | @insert a s ha ih =>
      have heq : (⋃ i ∈ insert a s, S i) = S a ∪ ⋃ i ∈ s, S i := by
        ext x
        simp
      rw [heq]
      exact (hclosed a).union ih

/-- A finite CLOSED cover of a preconnected trace supplies real region
connectivity. The covering sets need not themselves be connected. -/
theorem region_walk_of_preconnected_closed_cover
    {V ι : Type*} [TopologicalSpace V] [Fintype ι]
    (S : ι → Set V) (hclosed : ∀ i, IsClosed (S i))
    (K : Set V) (hK : IsPreconnected K)
    (hcover : ∀ x ∈ K, ∃ i, x ∈ S i)
    {u v : V} (huK : u ∈ K) (hvK : v ∈ K)
    (i j : ι) (hui : u ∈ S i) (hvj : v ∈ S j) :
    Nonempty ((intersectionGraph S).Walk i j) := by
  classical
  by_contra hnot
  let A : Finset ι := Finset.univ.filter
    (fun k => Nonempty ((intersectionGraph S).Walk i k))
  let B : Finset ι := Finset.univ.filter
    (fun k => ¬ Nonempty ((intersectionGraph S).Walk i k))
  let U : Set V := ⋃ k ∈ A, S k
  let W : Set V := ⋃ k ∈ B, S k
  have hiA : i ∈ A := by
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨.nil⟩
  have hjB : j ∈ B := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnot⟩
  have hU : IsClosed U := finite_closed_region_union S hclosed A
  have hW : IsClosed W := finite_closed_region_union S hclosed B
  have hKW : K ⊆ U ∪ W := by
    intro x hx
    obtain ⟨k, hk⟩ := hcover x hx
    by_cases hr : Nonempty ((intersectionGraph S).Walk i k)
    · have hkA : k ∈ A := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr⟩
      exact Or.inl (mem_iUnion.mpr ⟨k, mem_iUnion.mpr ⟨hkA, hk⟩⟩)
    · have hkB : k ∈ B := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr⟩
      exact Or.inr (mem_iUnion.mpr ⟨k, mem_iUnion.mpr ⟨hkB, hk⟩⟩)
  have huU : u ∈ U := mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hiA, hui⟩⟩
  have hvW : v ∈ W := mem_iUnion.mpr ⟨j, mem_iUnion.mpr ⟨hjB, hvj⟩⟩
  obtain ⟨z, _, hzU, hzW⟩ :=
    (isPreconnected_closed_iff.mp hK) U W hU hW hKW ⟨u, huK, huU⟩ ⟨v, hvK, hvW⟩
  obtain ⟨a, haA, hza⟩ := mem_iUnion₂.mp hzU
  obtain ⟨b, hbB, hzb⟩ := mem_iUnion₂.mp hzW
  have ha : Nonempty ((intersectionGraph S).Walk i a) :=
    (Finset.mem_filter.mp haA).2
  have hb : ¬ Nonempty ((intersectionGraph S).Walk i b) :=
    (Finset.mem_filter.mp hbB).2
  obtain ⟨p⟩ := ha
  obtain ⟨q⟩ := shared_point_walk S hza hzb
  exact hb ⟨p.append q⟩

/-- Transfer an actual face-intersection walk to a parent-vertex portal walk. -/
lemma face_walk_to_parent_vertex_walk
    {d : ℕ} {ι : Type*}
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (F : ι → Set (EuclideanSpace ℝ (Fin d)))
    (hP : IsCompact P) (hF : ∀ i, IsExtreme ℝ P (F i))
    (hclosed : ∀ i, IsClosed (F i))
    {i j : ι} (p : (intersectionGraph F).Walk i j) :
    Nonempty ((intersectionGraph (fun k => extremePoints ℝ P ∩ F k)).Walk i j) := by
  induction p with
  | nil => exact ⟨.nil⟩
  | @cons i k j hik p ih =>
      obtain ⟨z, hzi, hzk⟩ := hik.2
      obtain ⟨v, hv, hvi, hvk⟩ := compact_faces_shared_point_portal
        P (F i) (F k) hP (hF i) (hF k) (hclosed i) (hclosed k) z hzi hzk
      obtain ⟨q⟩ := ih
      exact ⟨.cons ⟨hik.1, v, ⟨hv, hvi⟩, ⟨hv, hvk⟩⟩ q⟩

/-- A genuine connected trace covered by finitely many closed parent faces
routes with one charge per face. There is no checkpoint partition assumption. -/
theorem route_of_preconnected_face_cover
    {d : ℕ} {ι : Type*} [Fintype ι]
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (F : ι → Set (EuclideanSpace ℝ (Fin d))) (B : ι → ℕ)
    (hP : IsCompact P) (hF : ∀ i, IsExtreme ℝ P (F i))
    (hclosed : ∀ i, IsClosed (F i)) (hD : ∀ i, DiamLE (F i) (B i))
    (K : Set (EuclideanSpace ℝ (Fin d))) (hK : IsPreconnected K)
    (hcover : ∀ x ∈ K, ∃ i, x ∈ F i)
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ P) (hv : v ∈ extremePoints ℝ P)
    (huK : u ∈ K) (hvK : v ∈ K) :
    Route (Adj P) (∑ i, B i) u v := by
  obtain ⟨i, hui⟩ := hcover u huK
  obtain ⟨j, hvj⟩ := hcover v hvK
  obtain ⟨p⟩ := region_walk_of_preconnected_closed_cover F hclosed K hK hcover huK hvK i j hui hvj
  exact route_of_connected_regions (Adj P) (fun i => extremePoints ℝ P ∩ F i) B
    (fun i => extreme_face_region P (F i) (B i) (hF i) (hD i))
    (face_walk_to_parent_vertex_walk P F hP hF hclosed p) u v ⟨hu, hui⟩ ⟨hv, hvj⟩


end HirschRegionRoute
end


-- BEGIN Solutions/PolynomialConvexSubsegment.lean

open scoped RealInnerProductSpace
open Set Hirsch

noncomputable section

namespace HirschSubsegment

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

def linePoint (p q : E) (t : ℝ) : E := (1 - t) • p + t • q

lemma linePoint_combo (p q : E) (a b t : ℝ) :
    (1 - t) • linePoint p q a + t • linePoint p q b =
      linePoint p q ((1 - t) * a + t * b) := by
  simp only [linePoint]
  module

lemma linePoint_mem_segment (p q : E) {a b c : ℝ}
    (hab : a < b) (ha : a ≤ c) (hb : c ≤ b) :
    linePoint p q c ∈ segment ℝ (linePoint p q a) (linePoint p q b) := by
  let t : ℝ := (c - a) / (b - a)
  have ht0 : 0 ≤ t := div_nonneg (sub_nonneg.mpr ha) (sub_pos.mpr hab).le
  have ht1 : t ≤ 1 := (div_le_iff₀ (sub_pos.mpr hab)).mpr (by linarith)
  have hmul : t * (b - a) = c - a := div_mul_cancel₀ _ (sub_pos.mpr hab).ne'
  have hparam : (1 - t) * a + t * b = c := by nlinarith
  refine ⟨1 - t, t, sub_nonneg.mpr ht1, ht0, by ring, ?_⟩
  rw [linePoint_combo, hparam]

lemma linePoint_mem_openSegment (p q : E) {a b c : ℝ}
    (ha : a < c) (hb : c < b) :
    linePoint p q c ∈ openSegment ℝ (linePoint p q a) (linePoint p q b) := by
  have hab : a < b := ha.trans hb
  let t : ℝ := (c - a) / (b - a)
  have ht0 : 0 < t := div_pos (sub_pos.mpr ha) (sub_pos.mpr hab)
  have ht1 : t < 1 := (div_lt_iff₀ (sub_pos.mpr hab)).mpr (by linarith)
  have hmul : t * (b - a) = c - a := div_mul_cancel₀ _ (sub_pos.mpr hab).ne'
  have hparam : (1 - t) * a + t * b = c := by nlinarith
  refine ⟨1 - t, t, sub_pos.mpr ht1, ht0, by ring, ?_⟩
  rw [linePoint_combo, hparam]

lemma segment_point_parameter (p q : E) {x : E} (hx : x ∈ segment ℝ p q) :
    ∃ t : ℝ, linePoint p q t = x := by
  obtain ⟨a, b, _, _, hab, hx⟩ := hx
  refine ⟨b, ?_⟩
  have ha : a = 1 - b := by linarith
  simpa [linePoint, ha] using hx

lemma subset_of_ordered_extreme_parameters (S : Set E) (p q : E)
    (hsub : S ⊆ segment ℝ p q) {a b : ℝ} (hab : a < b)
    (ha : linePoint p q a ∈ extremePoints ℝ S)
    (hb : linePoint p q b ∈ extremePoints ℝ S)
    (hne : linePoint p q a ≠ linePoint p q b) :
    S ⊆ segment ℝ (linePoint p q a) (linePoint p q b) := by
  intro z hz
  obtain ⟨c, hc⟩ := segment_point_parameter p q (hsub hz)
  have hz' : linePoint p q c ∈ S := hc.symm ▸ hz
  have hac : a ≤ c := by
    by_contra h
    have hca : c < a := lt_of_not_ge h
    have hop := linePoint_mem_openSegment p q hca hab
    have hba : linePoint p q b = linePoint p q a :=
      ha.2 hb.1 hz' (by rw [openSegment_symm]; exact hop)
    exact hne hba.symm
  have hcb : c ≤ b := by
    by_contra h
    have hbc : b < c := lt_of_not_ge h
    exact hne (hb.2 ha.1 hz' (linePoint_mem_openSegment p q hab hbc))
  exact hc ▸ linePoint_mem_segment p q hab hac hcb

/-- Every convex subset of a segment has graph diameter at most one. -/
theorem diamLE_of_convex_subsegment
    (S : Set E) (hS : Convex ℝ S) (p q : E) (hsub : S ⊆ segment ℝ p q) :
    DiamLE S 1 := by
  intro u hu v hv
  by_cases huv : u = v
  · subst v
    exact ⟨fun _ => u, rfl, rfl, fun _ _ => Or.inl rfl⟩
  obtain ⟨a, ha⟩ := segment_point_parameter p q (hsub hu.1)
  obtain ⟨b, hb⟩ := segment_point_parameter p q (hsub hv.1)
  have hab : a ≠ b := by
    intro h
    exact huv (ha.symm.trans ((congrArg (linePoint p q) h).trans hb))
  have hsub' : S ⊆ segment ℝ u v := by
    rcases lt_or_gt_of_ne hab with h | h
    · simpa [ha, hb] using subset_of_ordered_extreme_parameters S p q hsub h
        (ha.symm ▸ hu) (hb.symm ▸ hv) (by simpa [ha, hb] using huv)
    · have h' := subset_of_ordered_extreme_parameters S p q hsub h
        (hb.symm ▸ hv) (ha.symm ▸ hu)
        (by simpa [ha, hb] using (Ne.symm huv))
      simpa [ha, hb, segment_symm] using h'
  have heq : segment ℝ u v = S := (hS.segment_subset hu.1 hv.1).antisymm hsub'
  have hadj : Adj S u v := ⟨huv, heq.symm ▸ (IsExtreme.rfl : IsExtreme ℝ S S)⟩
  exact HirschRegionRoute.route_one (Adj S) (Or.inr hadj)

lemma extreme_inter_of_parent_subset (Q P F : Set E)
    (hPQ : P ⊆ Q) (hF : IsExtreme ℝ Q F) :
    IsExtreme ℝ P (P ∩ F) := by
  refine ⟨inter_subset_left, ?_⟩
  intro x hx y hy z hz hseg
  exact ⟨hx, hF.left_mem_of_mem_openSegment (hPQ hx) (hPQ hy) hz.2 hseg⟩


end HirschSubsegment
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


-- BEGIN Solutions/PolynomialRadialRetraction.lean

open scoped RealInnerProductSpace
open Set Hirsch

noncomputable section

namespace HirschRadial

variable {d : ℕ} {ι : Type*} [Fintype ι]

/-- A nonempty finite maximum with a constant-one entry, including empty ι. -/
def scale (r : ι → ℝ) : ℝ :=
  (Finset.univ : Finset (Option ι)).sup'
    ⟨none, Finset.mem_univ _⟩ (fun j => j.elim 1 r)

lemma one_le_scale (r : ι → ℝ) : 1 ≤ scale r := by
  exact Finset.le_sup' (fun j : Option ι => j.elim 1 r) (Finset.mem_univ none)

lemma le_scale (r : ι → ℝ) (i : ι) : r i ≤ scale r := by
  exact Finset.le_sup' (fun j : Option ι => j.elim 1 r) (Finset.mem_univ (some i))

lemma scale_le (r : ι → ℝ) {c : ℝ} (h1 : 1 ≤ c) (hr : ∀ i, r i ≤ c) :
    scale r ≤ c := by
  apply Finset.sup'_le
  intro j _
  cases j with
  | none => exact h1
  | some i => exact hr i

lemma scale_eq_one_or_row (r : ι → ℝ) : scale r = 1 ∨ ∃ i, scale r = r i := by
  obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_sup'
    (s := (Finset.univ : Finset (Option ι)))
    ⟨none, Finset.mem_univ _⟩ (fun j => j.elim 1 r)
  cases j with
  | none => exact Or.inl hj
  | some i => exact Or.inr ⟨i, hj⟩

lemma continuous_scale {X : Type*} [TopologicalSpace X]
    (r : ι → X → ℝ) (hr : ∀ i, Continuous (r i)) :
    Continuous (fun x => scale (fun i => r i x)) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  apply Filter.Tendsto.finset_sup'_nhds_apply
  intro j _
  cases j with
  | none => exact tendsto_const_nhds
  | some i => exact (hr i).continuousAt

def row (a : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] ℝ where
  toFun x := ⟪a, x⟫
  map_add' := by intros; simp [inner_add_right]
  map_smul' := by intros; simp [inner_smul_right]

def normalizedRow (a : EuclideanSpace ℝ (Fin d)) (b : ℝ)
    (o x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  (⟪a, x⟫ - ⟪a, o⟫) / (b - ⟪a, o⟫)

def clipSet (Q : Set (EuclideanSpace ℝ (Fin d)))
    (a : ι → EuclideanSpace ℝ (Fin d)) (b : ι → ℝ) :
    Set (EuclideanSpace ℝ (Fin d)) := Q ∩ {x | ∀ i, ⟪a i, x⟫ ≤ b i}

def retract (a : ι → EuclideanSpace ℝ (Fin d)) (b : ι → ℝ)
    (o x : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  point o x (scale (fun i => normalizedRow (a i) (b i) o x))

lemma continuous_retract (a : ι → EuclideanSpace ℝ (Fin d)) (b : ι → ℝ)
    (o : EuclideanSpace ℝ (Fin d)) : Continuous (retract a b o) := by
  have hc : Continuous (fun x => scale (fun i => normalizedRow (a i) (b i) o x)) := by
    apply continuous_scale
    intro i
    unfold normalizedRow
    fun_prop
  have hne : ∀ x, scale (fun i => normalizedRow (a i) (b i) o x) ≠ 0 := by
    intro x
    exact ne_of_gt (lt_of_lt_of_le zero_lt_one (one_le_scale _))
  exact continuous_const.add ((hc.inv₀ hne).smul (continuous_id.sub continuous_const))

lemma retract_mem (Q : Set (EuclideanSpace ℝ (Fin d))) (hQ : Convex ℝ Q)
    (a : ι → EuclideanSpace ℝ (Fin d)) (b : ι → ℝ)
    (o x : EuclideanSpace ℝ (Fin d)) (ho : o ∈ Q) (hx : x ∈ Q)
    (hstrict : ∀ i, ⟪a i, o⟫ < b i) : retract a b o x ∈ clipSet Q a b := by
  apply point_mem_final_clip Q hQ (fun i => row (a i)) b o x ho hx hstrict (one_le_scale _)
  intro i
  change normalizedRow (a i) (b i) o x ≤ scale (fun j => normalizedRow (a j) (b j) o x)
  exact le_scale (fun j => normalizedRow (a j) (b j) o x) i

lemma retract_fixes (a : ι → EuclideanSpace ℝ (Fin d)) (b : ι → ℝ)
    (o x : EuclideanSpace ℝ (Fin d))
    (hstrict : ∀ i, ⟪a i, o⟫ < b i) (hx : ∀ i, ⟪a i, x⟫ ≤ b i) :
    retract a b o x = x := by
  have hm : scale (fun i => normalizedRow (a i) (b i) o x) = 1 := by
    apply le_antisymm (scale_le _ (le_refl _) ?_) (one_le_scale _)
    intro i
    apply (div_le_iff₀ (sub_pos.mpr (hstrict i))).mpr
    linarith [hx i]
  simp [retract, hm, point_at_unit_scale]

lemma retract_eq_self_or_on_cut
    (a : ι → EuclideanSpace ℝ (Fin d)) (b : ι → ℝ)
    (o x : EuclideanSpace ℝ (Fin d))
    (hstrict : ∀ i, ⟪a i, o⟫ < b i) :
    retract a b o x = x ∨ ∃ i, ⟪a i, retract a b o x⟫ = b i := by
  rcases scale_eq_one_or_row (fun i => normalizedRow (a i) (b i) o x) with h | ⟨i, hi⟩
  · exact Or.inl (by simp [retract, h, point_at_unit_scale])
  · exact Or.inr ⟨i, point_mem_active_final_face (row (a i)) (b i) o x
      (hstrict i) (one_le_scale _) hi⟩

lemma retract_on_cut_of_exceeded
    (a : ι → EuclideanSpace ℝ (Fin d)) (b : ι → ℝ)
    (o x : EuclideanSpace ℝ (Fin d))
    (hstrict : ∀ i, ⟪a i, o⟫ < b i)
    (j : ι) (hj : b j ≤ ⟪a j, x⟫) :
    ∃ i, ⟪a i, retract a b o x⟫ = b i := by
  rcases scale_eq_one_or_row (fun i => normalizedRow (a i) (b i) o x) with h | ⟨i, hi⟩
  · have hle := le_scale (fun i => normalizedRow (a i) (b i) o x) j
    rw [h] at hle
    have hraw : ⟪a j, x⟫ - ⟪a j, o⟫ ≤ 1 * (b j - ⟪a j, o⟫) :=
      (div_le_iff₀ (sub_pos.mpr (hstrict j))).mp hle
    have heq : ⟪a j, x⟫ = b j := by linarith
    exact ⟨j, by simpa [retract, h, point_at_unit_scale] using heq⟩
  · exact ⟨i, point_mem_active_final_face (row (a i)) (b i) o x
      (hstrict i) (one_le_scale _) hi⟩


end HirschRadial
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


-- BEGIN Solutions/PolynomialClipEndpointLift.lean

open scoped RealInnerProductSpace
open Set Hirsch

noncomputable section

namespace HirschClipLift

variable {d : ℕ} {ι : Type*} [Fintype ι]

lemma supporting_equality_extreme
    (Q : Set (EuclideanSpace ℝ (Fin d))) (c : EuclideanSpace ℝ (Fin d)) (b : ℝ)
    (hbound : ∀ x ∈ Q, ⟪c, x⟫ ≤ b) :
    IsExtreme ℝ Q (Q ∩ {x | ⟪c, x⟫ = b}) := by
  refine ⟨inter_subset_left, ?_⟩
  intro x hx y hy z hz hseg
  refine ⟨hx, ?_⟩
  obtain ⟨α, β, hα, hβ, hsum, heq⟩ := hseg
  have heval := congrArg (fun w : EuclideanSpace ℝ (Fin d) => ⟪c, w⟫) heq
  simp only [inner_add_right, inner_smul_right] at heval
  have hz' : ⟪c, z⟫ = b := hz.2
  have hx' := hbound x hx
  have hy' := hbound y hy
  have htotal : α * b + β * b = b := by rw [← add_mul, hsum, one_mul]
  apply le_antisymm hx'
  by_contra h
  have hlt : ⟪c, x⟫ < b := lt_of_not_ge h
  have hpos := mul_pos hα (sub_pos.mpr hlt)
  have hnonneg := mul_nonneg hβ.le (sub_nonneg.mpr hy')
  nlinarith

lemma exists_extreme_above
    (Q : Set (EuclideanSpace ℝ (Fin d))) (hQ : IsCompact Q)
    (c u : EuclideanSpace ℝ (Fin d)) (hu : u ∈ Q) :
    ∃ x, x ∈ extremePoints ℝ Q ∧ ⟪c, u⟫ ≤ ⟪c, x⟫ := by
  obtain ⟨z, hz, hmax⟩ := hQ.exists_isMaxOn ⟨u, hu⟩
    (show Continuous (fun x : EuclideanSpace ℝ (Fin d) => ⟪c, x⟫) by fun_prop).continuousOn
  let F : Set (EuclideanSpace ℝ (Fin d)) := Q ∩ {x | ⟪c, x⟫ = ⟪c, z⟫}
  have hF : IsExtreme ℝ Q F := supporting_equality_extreme Q c ⟪c, z⟫ hmax
  have hFc : IsClosed F := hQ.isClosed.inter (isClosed_eq (by fun_prop) continuous_const)
  obtain ⟨x, hx, hxF⟩ := HirschRegionRoute.compact_face_point_has_parent_vertex
    Q F hQ hF hFc ⟨z, hz, rfl⟩
  exact ⟨x, hx, (hmax hu).trans_eq hxF.2.symm⟩

lemma strict_all_cuts_extreme_to_parent
    (Q : Set (EuclideanSpace ℝ (Fin d))) (hQ : Convex ℝ Q)
    (a : ι → EuclideanSpace ℝ (Fin d)) (b : ι → ℝ)
    {u : EuclideanSpace ℝ (Fin d)}
    (hu : u ∈ extremePoints ℝ (HirschRadial.clipSet Q a b))
    (hstrict : ∀ i, ⟪a i, u⟫ < b i) :
    u ∈ extremePoints ℝ Q := by
  classical
  let T : Finset ι → Set (EuclideanSpace ℝ (Fin d)) :=
    fun s => Q ∩ {x | ∀ i ∈ s, ⟪a i, x⟫ ≤ b i}
  have hconv : ∀ s, Convex ℝ (T s) := by
    intro s x hx y hy α β hα hβ hsum
    refine ⟨hQ hx.1 hy.1 hα hβ hsum, ?_⟩
    intro i hi
    simp only [inner_add_right, inner_smul_right]
    have h1 := mul_le_mul_of_nonneg_left (hx.2 i hi) hα
    have h2 := mul_le_mul_of_nonneg_left (hy.2 i hi) hβ
    have htotal : α * b i + β * b i = b i := by rw [← add_mul, hsum, one_mul]
    linarith
  have hremove : ∀ s, u ∈ extremePoints ℝ (T s) → u ∈ extremePoints ℝ Q := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa [T] using (id : u ∈ extremePoints ℝ Q → u ∈ extremePoints ℝ Q)
    | @insert i s hi ih =>
        intro huT
        have heq : T (insert i s) = T s ∩ {x | ⟪a i, x⟫ ≤ b i} := by
          ext x
          simp only [T, Set.mem_inter_iff, Set.mem_setOf_eq, Finset.mem_insert]
          aesop
        rw [heq] at huT
        exact ih (HirschCut.strict_cut_extreme_to_parent (T s) (hconv s)
          (a i) (b i) huT (hstrict i))
  apply hremove Finset.univ
  simpa [T, HirschRadial.clipSet] using hu

/-- Lift every final vertex to an old vertex beyond an active cut, unless
it already is an old vertex. No old vertex need survive the final clipping. -/
theorem endpoint_lift_to_outer_vertex
    (Q : Set (EuclideanSpace ℝ (Fin d))) (hQc : IsCompact Q) (hQ : Convex ℝ Q)
    (a : ι → EuclideanSpace ℝ (Fin d)) (b : ι → ℝ)
    (u : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (HirschRadial.clipSet Q a b)) :
    ∃ x, x ∈ extremePoints ℝ Q ∧
      (u = x ∨ ∃ i, ⟪a i, u⟫ = b i ∧ b i ≤ ⟪a i, x⟫) := by
  classical
  by_cases hold : u ∈ extremePoints ℝ Q
  · exact ⟨u, hold, Or.inl rfl⟩
  have hactive : ∃ i, ⟪a i, u⟫ = b i := by
    by_contra h
    have hne : ∀ i, ⟪a i, u⟫ ≠ b i := by simpa using h
    have hs : ∀ i, ⟪a i, u⟫ < b i := by
      intro i
      rcases (hu.1.2 i).eq_or_lt with heq | hlt
      · exact False.elim (hne i heq)
      · exact hlt
    exact hold (strict_all_cuts_extreme_to_parent Q hQ a b hu hs)
  obtain ⟨i, hi⟩ := hactive
  obtain ⟨x, hx, hux⟩ := exists_extreme_above Q hQc (a i) u hu.1.1
  exact ⟨x, hx, Or.inr ⟨i, hi, by simpa [hi] using hux⟩⟩


end HirschClipLift
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


-- BEGIN Solutions/PolynomialSimultaneousClipDiameter.lean

/-! Simultaneous clipping with FINAL face budgets and newly created endpoints.
Verification status is recorded in research/ClippingVerificationProgress.md. -/

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

noncomputable section

namespace HirschRadial

variable {d : ℕ} {ι : Type*} [Fintype ι]

lemma clipSet_convex (Q : Set (EuclideanSpace ℝ (Fin d))) (hQ : Convex ℝ Q)
    (a : ι → EuclideanSpace ℝ (Fin d)) (b : ι → ℝ) : Convex ℝ (clipSet Q a b) := by
  intro x hx y hy α β hα hβ hsum
  refine ⟨hQ hx.1 hy.1 hα hβ hsum, ?_⟩
  intro i
  simp only [inner_add_right, inner_smul_right]
  have htotal : α * b i + β * b i = b i := by rw [← add_mul, hsum, one_mul]
  linarith [mul_le_mul_of_nonneg_left (hx.2 i) hα,
    mul_le_mul_of_nonneg_left (hy.2 i) hβ]

lemma clipSet_compact (Q : Set (EuclideanSpace ℝ (Fin d))) (hQ : IsCompact Q)
    (a : ι → EuclideanSpace ℝ (Fin d)) (b : ι → ℝ) : IsCompact (clipSet Q a b) := by
  have hclosed : IsClosed {x : EuclideanSpace ℝ (Fin d) | ∀ i, ⟪a i, x⟫ ≤ b i} := by
    have heq : {x : EuclideanSpace ℝ (Fin d) | ∀ i, ⟪a i, x⟫ ≤ b i} =
        ⋂ i, {x | ⟪a i, x⟫ ≤ b i} := by ext x; simp
    rw [heq]
    exact isClosed_iInter (fun i => isClosed_le (by fun_prop) continuous_const)
  exact hQ.inter_right hclosed

def walkTrace (w : ℕ → EuclideanSpace ℝ (Fin d)) : ℕ → Set (EuclideanSpace ℝ (Fin d))
  | 0 => {w 0}
  | n + 1 => walkTrace w n ∪ segment ℝ (w n) (w (n + 1))

lemma walkTrace_start (w : ℕ → EuclideanSpace ℝ (Fin d)) (L : ℕ) : w 0 ∈ walkTrace w L := by
  induction L with
  | zero => exact mem_singleton _
  | succ L ih => exact Or.inl ih

lemma walkTrace_end (w : ℕ → EuclideanSpace ℝ (Fin d)) (L : ℕ) : w L ∈ walkTrace w L := by
  cases L with
  | zero => exact mem_singleton _
  | succ L => exact Or.inr (right_mem_segment ℝ _ _)

lemma walkTrace_preconnected (w : ℕ → EuclideanSpace ℝ (Fin d)) (L : ℕ) :
    IsPreconnected (walkTrace w L) := by
  induction L with
  | zero => exact isPreconnected_singleton
  | succ L ih =>
      exact ih.union (w L) (walkTrace_end w L) (left_mem_segment ℝ _ _)
        (convex_segment (w L) (w (L + 1))).isPreconnected

lemma singleton_diamLE_zero (u : EuclideanSpace ℝ (Fin d)) : DiamLE ({u} : Set _) 0 := by
  intro x hx y hy
  have hx' : x = u := by simpa using hx
  have hy' : y = u := by simpa using hy
  subst x
  subst y
  exact ⟨fun _ => u, rfl, rfl, fun _ h => False.elim (Nat.not_lt_zero _ h)⟩

/-- The endpoint spokes and the middle route charge the same final face family
only once. Only compactness and the explicit outer/face budgets are assumed. -/
theorem diamLE_clip_of_strict_centre
    (Q : Set (EuclideanSpace ℝ (Fin d))) (hQc : IsCompact Q) (hQ : Convex ℝ Q)
    (a : ι → EuclideanSpace ℝ (Fin d)) (b : ι → ℝ)
    (D : ℕ) (B : ι → ℕ) (hD : DiamLE Q D)
    (hFaces : ∀ i, DiamLE (clipSet Q a b ∩ {z | ⟪a i, z⟫ = b i}) (B i))
    (o : EuclideanSpace ℝ (Fin d)) (ho : o ∈ Q) (hstrict : ∀ i, ⟪a i, o⟫ < b i) :
    DiamLE (clipSet Q a b) (D + ∑ i, B i) := by
  classical
  let P := clipSet Q a b
  have hPc : IsCompact P := clipSet_compact Q hQc a b
  have hPv : Convex ℝ P := clipSet_convex Q hQ a b
  intro u hu v hv
  obtain ⟨x, hx, hux⟩ := HirschClipLift.endpoint_lift_to_outer_vertex Q hQc hQ a b u hu
  obtain ⟨y, hy, hvy⟩ := HirschClipLift.endpoint_lift_to_outer_vertex Q hQc hQ a b v hv
  obtain ⟨w, hw0, hwD, hstep⟩ := hD x hx y hy
  have hwv : ∀ k ≤ D, w k ∈ extremePoints ℝ Q := by
    intro k
    induction k with
    | zero => intro _; simpa [hw0] using hx
    | succ k ih =>
        intro hk
        rcases hstep k (by omega) with heq | hedge
        · rw [← heq]
          exact ih (by omega)
        · exact HirschPolynomialAccess.adj_right_extreme Q hedge
  have hOld : ∀ k : Fin D, IsExtreme ℝ Q (segment ℝ (w k.val) (w (k.val + 1))) := by
    intro k
    rcases hstep k.val k.isLt with heq | hedge
    · rw [heq, segment_same]
      exact isExtreme_singleton.mpr (hwv (k.val + 1) (by omega))
    · exact hedge.2
  let F : Sum ι (Sum (Fin D) (Fin 2)) → Set (EuclideanSpace ℝ (Fin d))
    | .inl i => P ∩ {z | ⟪a i, z⟫ = b i}
    | .inr (.inl k) => P ∩ segment ℝ (w k.val) (w (k.val + 1))
    | .inr (.inr k) => {if k = 0 then u else v}
  let C : Sum ι (Sum (Fin D) (Fin 2)) → ℕ
    | .inl i => B i
    | .inr (.inl _) => 1
    | .inr (.inr _) => 0
  have hF : ∀ k, IsExtreme ℝ P (F k) := by
    intro k
    rcases k with i | (e | t)
    · exact HirschClipLift.supporting_equality_extreme P (a i) (b i)
        (fun z hz => hz.2 i)
    · exact HirschSubsegment.extreme_inter_of_parent_subset Q P _
        inter_subset_left (hOld e)
    · by_cases ht : t = 0
      · simpa [F, ht] using (isExtreme_singleton.mpr hu)
      · simpa [F, ht] using (isExtreme_singleton.mpr hv)
  have hFc : ∀ k, IsClosed (F k) := by
    intro k
    rcases k with i | (e | t)
    · exact hPc.isClosed.inter (isClosed_eq (by fun_prop) continuous_const)
    · apply hPc.isClosed.inter
      have hc : IsCompact (segment ℝ (w e.val) (w (e.val + 1))) := by
        rw [segment_eq_image]
        exact isCompact_Icc.image (by fun_prop)
      exact hc.isClosed
    · exact isClosed_singleton
  have hFD : ∀ k, DiamLE (F k) (C k) := by
    intro k
    rcases k with i | (e | t)
    · exact hFaces i
    · exact HirschSubsegment.diamLE_of_convex_subsegment _
        (hPv.inter (convex_segment _ _)) _ _ inter_subset_right
    · exact singleton_diamLE_zero _
  let ρ := retract a b o
  have hρP : ∀ z ∈ Q, ρ z ∈ P := fun z hz => retract_mem Q hQ a b o z ho hz hstrict
  have hρfix : ∀ z ∈ P, ρ z = z := fun z hz => retract_fixes a b o z hstrict hz.2
  have hspoke : ∀ (e z : EuclideanSpace ℝ (Fin d)), e ∈ P → z ∈ Q →
      (e = z ∨ ∃ i, ⟪a i, e⟫ = b i ∧ b i ≤ ⟪a i, z⟫) →
      (∃ k : Fin 2, e = if k = 0 then u else v) →
      ∀ t ∈ segment ℝ e z, ∃ k, ρ t ∈ F k := by
    intro e z he hz hez hend t ht
    rcases hez with heq | ⟨i, hei, hzi⟩
    · have hte : t = e := by simpa [← heq] using ht
      obtain ⟨k, hk⟩ := hend
      refine ⟨.inr (.inr k), ?_⟩
      change ρ t = if k = 0 then u else v
      exact (congrArg ρ hte).trans ((hρfix e he).trans hk)
    · have htQ : t ∈ Q := hQ.segment_subset he.1 hz ht
      have hit : b i ≤ ⟪a i, t⟫ := by
        obtain ⟨α, β, hα, hβ, hsum, heval⟩ := ht
        have h := congrArg (fun z : EuclideanSpace ℝ (Fin d) => ⟪a i, z⟫) heval
        simp only [inner_add_right, inner_smul_right] at h
        have htotal : α * b i + β * b i = b i := by rw [← add_mul, hsum, one_mul]
        rw [hei] at h
        linarith [mul_le_mul_of_nonneg_left hzi hβ]
      obtain ⟨j, hj⟩ := retract_on_cut_of_exceeded a b o t hstrict i hit
      exact ⟨.inl j, hρP t htQ, hj⟩
  have hleft : ∀ t ∈ segment ℝ u x, ∃ k, ρ t ∈ F k :=
    hspoke u x hu.1 hx.1 hux ⟨0, by simp⟩
  have hright : ∀ t ∈ segment ℝ v y, ∃ k, ρ t ∈ F k :=
    hspoke v y hv.1 hy.1 hvy ⟨1, by simp⟩
  have htrace : ∀ L ≤ D, ∀ z ∈ walkTrace w L, ∃ k, ρ z ∈ F k := by
    intro L
    induction L with
    | zero =>
        intro _ z hz
        have hz0 : z = w 0 := hz
        subst z
        rw [hw0]
        exact hleft x (right_mem_segment ℝ _ _)
    | succ L ih =>
        intro hL z hz
        rcases hz with hz | hz
        · exact ih (by omega) z hz
        · have hzQ : z ∈ Q := hQ.segment_subset (hwv L (by omega)).1
            (hwv (L + 1) (by omega)).1 hz
          rcases retract_eq_self_or_on_cut a b o z hstrict with hfix | ⟨i, hi⟩
          · refine ⟨.inr (.inl ⟨L, by omega⟩), hρP z hzQ, ?_⟩
            simpa [ρ, hfix] using hz
          · exact ⟨.inl i, hρP z hzQ, hi⟩
  let K := (segment ℝ u x ∪ walkTrace w D) ∪ segment ℝ v y
  have hK : IsPreconnected K := by
    have h1 : IsPreconnected (segment ℝ u x ∪ walkTrace w D) :=
      (convex_segment u x).isPreconnected.union x (right_mem_segment ℝ _ _)
        (by simpa [hw0] using walkTrace_start w D) (walkTrace_preconnected w D)
    exact h1.union y (Or.inr (by simpa [hwD] using walkTrace_end w D))
      (right_mem_segment ℝ _ _) (convex_segment v y).isPreconnected
  have himage : IsPreconnected (ρ '' K) :=
    hK.image ρ (continuous_retract a b o).continuousOn
  have hcover : ∀ z ∈ ρ '' K, ∃ k, z ∈ F k := by
    rintro _ ⟨z, hz, rfl⟩
    rcases hz with (hz | hz) | hz
    · exact hleft z hz
    · exact htrace D (le_refl _) z hz
    · exact hright z hz
  have huK : u ∈ ρ '' K :=
    ⟨u, Or.inl (Or.inl (left_mem_segment ℝ _ _)), hρfix u hu.1⟩
  have hvK : v ∈ ρ '' K :=
    ⟨v, Or.inr (left_mem_segment ℝ _ _), hρfix v hv.1⟩
  have hr := HirschRegionRoute.route_of_preconnected_face_cover P F C hPc hF hFc hFD
    (ρ '' K) himage hcover u v hu hv huK hvK
  simpa [C, Fintype.sum_sum_type, Nat.add_comm] using hr

lemma strict_centre_or_universal_cut
    (P : Set (EuclideanSpace ℝ (Fin d))) (hP : Convex ℝ P) (hne : P.Nonempty)
    (a : ι → EuclideanSpace ℝ (Fin d)) (b : ι → ℝ)
    (hbound : ∀ i, ∀ x ∈ P, ⟪a i, x⟫ ≤ b i) :
    (∃ o ∈ P, ∀ i, ⟪a i, o⟫ < b i) ∨ (∃ i, ∀ x ∈ P, ⟪a i, x⟫ = b i) := by
  classical
  by_cases huniv : ∃ i, ∀ x ∈ P, ⟪a i, x⟫ = b i
  · exact Or.inr huniv
  have hpoint : ∀ i, ∃ x ∈ P, ⟪a i, x⟫ < b i := by
    intro i
    by_contra h
    push_neg at h
    apply huniv
    exact ⟨i, fun x hx => le_antisymm (hbound i x hx) (h x hx)⟩
  have hfinite : ∀ s : Finset ι, ∃ o ∈ P, ∀ i ∈ s, ⟪a i, o⟫ < b i := by
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
        simp only [inner_add_right, inner_smul_right]
        rcases Finset.mem_insert.mp hj with rfl | hj
        · nlinarith [hbound j o ho]
        · nlinarith [hs j hj, hbound j x hx]
  obtain ⟨o, ho, hs⟩ := hfinite Finset.univ
  exact Or.inl ⟨o, ho, fun i => hs i (Finset.mem_univ _)⟩

/-- All-vertex diameter transfer under simultaneous clipping by finitely many
halfspaces. Face budgets refer to the FINAL intersection, not intermediate sets. -/
theorem simultaneous_clipping_diameter_bound
    (Q : Set (EuclideanSpace ℝ (Fin d))) (hQc : IsCompact Q) (hQ : Convex ℝ Q)
    (a : ι → EuclideanSpace ℝ (Fin d)) (b : ι → ℝ)
    (D : ℕ) (B : ι → ℕ) (hD : DiamLE Q D)
    (hFaces : ∀ i, DiamLE (clipSet Q a b ∩ {z | ⟪a i, z⟫ = b i}) (B i)) :
    DiamLE (clipSet Q a b) (D + ∑ i, B i) := by
  classical
  let P := clipSet Q a b
  by_cases hne : P.Nonempty
  · rcases strict_centre_or_universal_cut P (clipSet_convex Q hQ a b) hne a b
        (fun i x hx => hx.2 i) with ⟨o, ho, hs⟩ | ⟨i, hi⟩
    · exact diamLE_clip_of_strict_centre Q hQc hQ a b D B hD hFaces o ho.1 hs
    · have heq : P ∩ {z | ⟪a i, z⟫ = b i} = P := by
        apply inter_eq_left.mpr
        exact fun z hz => hi z hz
      have hPi : DiamLE P (B i) := by
        have h := hFaces i
        change DiamLE (P ∩ {z | ⟪a i, z⟫ = b i}) (B i) at h
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


end HirschRadial
end


-- BEGIN Solutions/Sol_Hirsch_simultaneous_clipping_diameter_bound.lean

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

noncomputable section

/-- Public-type wrapper for simultaneous clipping with all final vertices allowed.
The statement exposes only the outer set and the final halfspace intersection;
`HirschRadial.clipSet` is expanded from the public theorem type. -/
theorem solution
    {d : ℕ} {ι : Type*} [Fintype ι]
    (Q : Set (EuclideanSpace ℝ (Fin d))) (hQc : IsCompact Q) (hQ : Convex ℝ Q)
    (a : ι → EuclideanSpace ℝ (Fin d)) (b : ι → ℝ)
    (D : ℕ) (B : ι → ℕ) (hD : DiamLE Q D)
    (hFaces : ∀ i,
      DiamLE ((Q ∩ {x | ∀ j, ⟪a j, x⟫ ≤ b j}) ∩ {z | ⟪a i, z⟫ = b i}) (B i)) :
    DiamLE (Q ∩ {x | ∀ i, ⟪a i, x⟫ ≤ b i}) (D + ∑ i, B i) := by
  simpa [HirschRadial.clipSet] using
    (HirschRadial.simultaneous_clipping_diameter_bound Q hQc hQ a b D B hD hFaces)

end


#print axioms solution
