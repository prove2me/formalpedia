-- Prove2me | solution 1 for Hirsch.geodesic_joint_budget_of_all_available_contacts
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-12T22:51:57.93833+00:00
-- url     : https://prove2.me/submissions/83ed9045-971b-4ad8-ae0d-3659c625e850

import Mathlib
open scoped BigOperators
open Set
namespace HirschRegionRoute
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


end HirschRegionRoute

/-!
# Every available label has a three-position window on a geodesic

Unlike chordlessness, metric minimality controls vertices OFF the path.
An off-path vertex adjacent to two positions more than two apart supplies
an inadmissible two-edge shortcut. Double counting therefore charges every
available label at most three times, including labels never selected.

New proof candidate: no Lean compilation or platform verdict is asserted.
-/
open scoped BigOperators
open Set
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace HirschRegionRoute

/-- Reflexive graph contact, used to include the currently selected row itself. -/
def ClosedNear {V : Type*} (G : SimpleGraph V) (x y : V) : Prop :=
  x = y ∨ G.Adj x y

lemma ClosedNear.symm {V : Type*} {G : SimpleGraph V} {x y : V}
    (h : ClosedNear G x y) : ClosedNear G y x := by
  rcases h with h | h
  · exact Or.inl h.symm
  · exact Or.inr h.symm

lemma closedNear_short_walk {V : Type*} {G : SimpleGraph V} {x y : V}
    (h : ClosedNear G x y) : ∃ q : G.Walk x y, q.length ≤ 1 := by
  rcases h with h | h
  · subst y
    exact ⟨.nil, by simp⟩
  · exact ⟨.cons h .nil, by simp⟩

/-- Any alternative between two positions of a shortest path is at least as
long as their index difference. This is not true for a merely induced path. -/
theorem geodesic_index_gap_le_walk
    {V : Type*} {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (hp : p.length = G.dist u v)
    (r s : ℕ) (hrs : r ≤ s) (hs : s ≤ p.length)
    (q : G.Walk (p.getVert r) (p.getVert s)) :
    s ≤ r + q.length := by
  have hr : r ≤ p.length := hrs.trans hs
  let shortcut : G.Walk u v := ((p.take r).append q).append (p.drop s)
  have hdist := SimpleGraph.dist_le shortcut
  have hlen : shortcut.length = r + q.length + (p.length - s) := by
    simp [shortcut, hr]
  rw [← hp, hlen] at hdist
  omega

/-- A vertex anywhere in the graph can contact only an index window of width
 two on a geodesic; it need not itself belong to the path. -/
theorem geodesic_closedNear_index_span
    {V : Type*} {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (hp : p.length = G.dist u v)
    (z : V) (r s : ℕ) (hrs : r ≤ s) (hs : s ≤ p.length)
    (hzr : ClosedNear G z (p.getVert r))
    (hzs : ClosedNear G z (p.getVert s)) : s ≤ r + 2 := by
  obtain ⟨q₁, h₁⟩ := closedNear_short_walk hzr.symm
  obtain ⟨q₂, h₂⟩ := closedNear_short_walk hzs
  have h := geodesic_index_gap_le_walk p hp r s hrs hs (q₁.append q₂)
  simp only [SimpleGraph.Walk.length_append] at h
  omega

/-- Path labels contacted by a fixed, possibly unused, graph vertex. -/
def geodesicContactSupport
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (z : V) : Finset V := by
  classical
  exact p.support.toFinset.filter (ClosedNear G z)

theorem geodesicContactSupport_card_le_three
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (hp : p.length = G.dist u v) (z : V) :
    (geodesicContactSupport p z).card ≤ 3 := by
  classical
  by_cases hn : (geodesicContactSupport p z).Nonempty
  · obtain ⟨x, hx, hmin⟩ := Finset.exists_min_image
      (geodesicContactSupport p z) (fun t => p.support.idxOf t) hn
    let r := p.support.idxOf x
    have hxs : x ∈ p.support := by
      simpa using (Finset.mem_filter.mp hx).1
    have hxr : p.getVert r = x := p.getVert_support_idxOf hxs
    have hsub : geodesicContactSupport p z ⊆
        ({p.getVert r, p.getVert (r+1), p.getVert (r+2)} : Finset V) := by
      intro y hy
      have hys : y ∈ p.support := by
        simpa using (Finset.mem_filter.mp hy).1
      let s := p.support.idxOf y
      have hys' : p.getVert s = y := p.getVert_support_idxOf hys
      have hrs : r ≤ s := hmin y hy
      have hslt : s < p.support.length := List.idxOf_lt_length_of_mem hys
      have hs : s ≤ p.length := by rw [p.length_support] at hslt; omega
      have hspan := geodesic_closedNear_index_span p hp z r s hrs hs
        (by simpa [hxr] using (Finset.mem_filter.mp hx).2)
        (by simpa [hys'] using (Finset.mem_filter.mp hy).2)
      have hcases : s = r ∨ s = r+1 ∨ s = r+2 := by omega
      rcases hcases with h | h | h
      · simp [← hys', h]
      · simp [← hys', h]
      · simp [← hys', h]
    have hthree : ({p.getVert r, p.getVert (r+1), p.getVert (r+2)} : Finset V).card ≤ 3 := by
      have h₁ := Finset.card_insert_le (p.getVert r)
        ({p.getVert (r+1), p.getVert (r+2)} : Finset V)
      have h₂ := Finset.card_insert_le (p.getVert (r+1))
        ({p.getVert (r+2)} : Finset V)
      simp only [Finset.card_singleton] at h₂
      omega
    exact (Finset.card_le_card hsub).trans hthree
  · have he : geodesicContactSupport p z = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    simp [he]

/-- Number of ALL available labels contacting one selected label. -/
def availableContactLoad {V : Type*} (G : SimpleGraph V)
    (available : Finset V) (i : V) : ℕ := by
  classical
  exact (available.filter (fun j => ClosedNear G j i)).card

/-- Double counting is the crucial new joint estimate. No assumption says
 that available labels are selected, or even lie on the path. -/
theorem geodesic_total_available_load
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (hp : p.length = G.dist u v)
    (available selected : Finset V)
    (hselected : selected ⊆ p.support.toFinset) :
    (∑ i ∈ selected, availableContactLoad G available i) ≤ 3 * available.card := by
  classical
  have hswap : (∑ i ∈ selected, availableContactLoad G available i) =
      ∑ j ∈ available, (selected.filter (ClosedNear G j)).card := by
    simp only [availableContactLoad, Finset.card_eq_sum_ones, Finset.sum_filter]
    exact Finset.sum_comm
  rw [hswap]
  have hcol : ∀ j ∈ available, (selected.filter (ClosedNear G j)).card ≤ 3 := by
    intro j _
    have hsub : selected.filter (ClosedNear G j) ⊆ geodesicContactSupport p j := by
      intro x hx
      obtain ⟨hxs, hxj⟩ := Finset.mem_filter.mp hx
      exact Finset.mem_filter.mpr ⟨hselected hxs, hxj⟩
    exact (Finset.card_le_card hsub).trans (geodesicContactSupport_card_le_three p hp j)
  simpa [Nat.mul_comm] using Finset.sum_le_sum hcol

/-- List form, for the duplicate-free labels of the actual clipping legs. -/
theorem geodesic_list_available_load
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (hp : p.length = G.dist u v)
    (available : Finset V) (labels : List V) (hnd : labels.Nodup)
    (hsub : ∀ i ∈ labels, i ∈ p.support) :
    (labels.map (availableContactLoad G available)).sum ≤ 3 * available.card := by
  have h₁ := nodup_cost_le (availableContactLoad G available) labels labels.toFinset
    hnd (by intro i hi; exact List.mem_toFinset.mpr hi)
  have h₂ := geodesic_total_available_load p hp available labels.toFinset (by
    intro i hi
    exact List.mem_toFinset.mpr (hsub i (List.mem_toFinset.mp hi)))
  exact h₁.trans h₂

/-- Subtraction-free summation; valid even when available.card exceeds e. -/
theorem list_sum_available_budget
    {α : Type*} (ls : List α) (delta load : α → ℕ) (s e : ℕ)
    (h : ∀ x ∈ ls, delta x + s ≤ e + load x) :
    (ls.map delta).sum + ls.length * s ≤ ls.length * e + (ls.map load).sum := by
  induction ls with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih (fun y hy => h y (by simp [hy]))
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
    omega

end HirschRegionRoute
end

theorem solution {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {u v : V} (p : G.Walk u v) (hp : p.length = G.dist u v)
    (available : Finset V) (labels : List V) (hnd : labels.Nodup)
    (hsub : ∀ i ∈ labels, i ∈ p.support) (delta : V → ℕ) (e : ℕ)
    (hbudget : ∀ i ∈ labels, delta i + available.card ≤ e +
      (available.filter (fun j => j = i ∨ G.Adj j i)).card) :
    (labels.map delta).sum + labels.length * available.card ≤
      labels.length * e + 3 * available.card := by
  classical
  have hpoint : ∀ i ∈ labels, delta i + available.card ≤
      e + HirschRegionRoute.availableContactLoad G available i := by
    intro i hi
    simpa only [HirschRegionRoute.availableContactLoad, HirschRegionRoute.ClosedNear] using hbudget i hi
  have hs := HirschRegionRoute.list_sum_available_budget labels delta
    (HirschRegionRoute.availableContactLoad G available) available.card e hpoint
  have hc := HirschRegionRoute.geodesic_list_available_load p hp available labels hnd hsub
  omega
