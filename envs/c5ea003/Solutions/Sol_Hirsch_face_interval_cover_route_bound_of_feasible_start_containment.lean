-- Prove2me | solution 1 for Hirsch.face_interval_cover_route_bound_of_feasible_start_containment
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-09T21:27:32.556665+00:00
-- url     : https://prove2.me/submissions/6c140ee2-141f-4b4f-baa3-031a31df4f7f

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


-- BEGIN Solutions/Sol_Hirsch_feasible_start_containment_route_bound.lean

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

noncomputable section

/-- Public wrapper: marked interval checkpoints may be nonvertices. Closed-face
membership and compactness allow simultaneous rounding while preserving all
incidences; only the two global route endpoints must initially be vertices. -/
theorem solution
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
    ∃ q : ℕ → EuclideanSpace ℝ (Fin d),
      q 0 = w 0 ∧ q (∑ i, B i) = w L ∧
      ∀ r < ∑ i, B i,
        q r = q (r + 1) ∨ Adj P (q r) (q (r + 1)) := by
  exact HirschRegionRoute.route_of_face_interval_cover_of_feasible_start_containment
    P F B hP hF hclosed hD s t w L hbound h0 hL hends hcover hcontain

end


#print axioms solution
