-- Prove2me | solution 1 for Hirsch.near_geodesic_occurrence_carrier_budget
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-12T23:24:40.361759+00:00
-- url     : https://prove2.me/submissions/1ede1000-2a0d-4d98-8736-1a828626eb2f

import Mathlib
open scoped BigOperators
open Set

/-!
# Additive-slack region paths retain bounded all-row incidence

Unlike a strict geodesic, a path at most q edges above the endpoint distance
may avoid an expensive portal. The same shortcut proof still puts every graph
vertex's contacts in q+3 consecutive path positions. Portal activity, using
the regions on BOTH sides of a portal, has the sharper span q+1.

New proof candidates. No new Lean compilation or platform verdict is asserted.
-/
open scoped BigOperators
open Set
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
namespace HirschPortalDebt

/-- Reflexive contact includes a row which is itself a path label. -/
def Contact {V : Type*} (G : SimpleGraph V) (x y : V) : Prop :=
  x = y ∨ G.Adj x y

lemma Contact.symm {V : Type*} {G : SimpleGraph V} {x y : V}
    (h : Contact G x y) : Contact G y x := by
  rcases h with h | h
  · exact Or.inl h.symm
  · exact Or.inr h.symm

lemma contact_walk {V : Type*} {G : SimpleGraph V} {x y : V}
    (h : Contact G x y) : ∃ w : G.Walk x y, w.length ≤ 1 := by
  rcases h with h | h
  · subst y
    exact ⟨.nil, by simp⟩
  · exact ⟨.cons h .nil, by simp⟩

/-- Positions far apart on a near-geodesic cannot share a graph neighbor. -/
theorem contact_index_span
    {V : Type*} {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (q : ℕ) (hp : p.length ≤ G.dist u v + q)
    (z : V) (r s : ℕ) (hrs : r ≤ s) (hs : s ≤ p.length)
    (hrz : Contact G z (p.getVert r))
    (hsz : Contact G z (p.getVert s)) : s ≤ r + q + 2 := by
  obtain ⟨a, ha⟩ := contact_walk hrz.symm
  obtain ⟨b, hb⟩ := contact_walk hsz
  have hr : r ≤ p.length := hrs.trans hs
  let w : G.Walk u v := ((p.take r).append (a.append b)).append (p.drop s)
  have hd := SimpleGraph.dist_le w
  have hl : w.length = r + (a.length + b.length) + (p.length-s) := by
    simp [w, hr]
  rw [hl] at hd
  omega

/-- A facet active at a portal contacts the labels on both sides of it.
Consequently two active portal indices differ by at most q+1, not q+2. -/
theorem active_portal_index_span
    {V : Type*} {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (q : ℕ) (hp : p.length ≤ G.dist u v + q)
    (z : V) (r s : ℕ) (hrs : r ≤ s) (hs : s+1 ≤ p.length)
    (hleft : Contact G z (p.getVert r))
    (hright : Contact G z (p.getVert (s+1))) : s ≤ r + q + 1 := by
  have h := contact_index_span p q hp z r (s+1) (by omega) hs hleft hright
  omega

/-- Counts positions, not distinct labels; no hidden path-nodup premise. -/
def contactPositions {V : Type*} {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (z : V) : Finset ℕ := by
  classical
  exact (Finset.range (p.length+1)).filter (fun k => Contact G z (p.getVert k))

theorem contactPositions_card_le
    {V : Type*} {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (q : ℕ) (hp : p.length ≤ G.dist u v + q) (z : V) :
    (contactPositions p z).card ≤ q+3 := by
  classical
  by_cases hn : (contactPositions p z).Nonempty
  · obtain ⟨r, hr, hmin⟩ := Finset.exists_min_image (contactPositions p z) id hn
    have hsub : contactPositions p z ⊆ Finset.Icc r (r+q+2) := by
      intro s hs
      have hrs : r ≤ s := hmin s hs
      have hrz := (Finset.mem_filter.mp hr).2
      have hsz := (Finset.mem_filter.mp hs).2
      have hslen : s ≤ p.length := by
        have h := Finset.mem_range.mp (Finset.mem_filter.mp hs).1
        omega
      exact Finset.mem_Icc.mpr ⟨hrs, contact_index_span p q hp z r s hrs hslen hrz hsz⟩
    have hc : (Finset.Icc r (r+q+2)).card = q+3 := by
      simp [Nat.card_Icc] <;> omega
    exact (Finset.card_le_card hsub).trans_eq hc
  · have he : contactPositions p z = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    simp [he]

def positionLoad {V : Type*} (G : SimpleGraph V)
    (available : Finset V) (i : V) : ℕ := by
  classical
  exact (available.filter (fun z => Contact G z i)).card

/-- Each original available row can be charged at most q+3 times at one level. -/
theorem total_position_load_le
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (q : ℕ) (hp : p.length ≤ G.dist u v + q)
    (available : Finset V) (positions : Finset ℕ)
    (hpositions : ∀ k ∈ positions, k ≤ p.length) :
    (∑ k ∈ positions, positionLoad G available (p.getVert k)) ≤ (q+3)*available.card := by
  classical
  have he : (∑ k ∈ positions, positionLoad G available (p.getVert k)) =
      ∑ z ∈ available, (positions.filter (fun k => Contact G z (p.getVert k))).card := by
    simp only [positionLoad, Finset.card_eq_sum_ones, Finset.sum_filter]
    exact Finset.sum_comm
  rw [he]
  have hcol : ∀ z ∈ available,
      (positions.filter (fun k => Contact G z (p.getVert k))).card ≤ q+3 := by
    intro z _
    have hsub : positions.filter (fun k => Contact G z (p.getVert k)) ⊆ contactPositions p z := by
      intro k hk
      obtain ⟨hk, hz⟩ := Finset.mem_filter.mp hk
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by have h := hpositions k hk; omega), hz⟩
    exact (Finset.card_le_card hsub).trans (contactPositions_card_le p q hp z)
  simpa [Nat.mul_comm] using Finset.sum_le_sum hcol

/-- Reuse the geometric pointwise disjoint-row budget from #206. The premise
is an intrinsic-row inequality, NOT a local route or diameter assumption. -/
theorem near_geodesic_carrier_mass
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (q : ℕ) (hp : p.length ≤ G.dist u v + q)
    (available : Finset V) (positions : Finset ℕ)
    (hpositions : ∀ k ∈ positions, k ≤ p.length)
    (delta : ℕ → ℕ) (e : ℕ)
    (hbudget : ∀ k ∈ positions,
      delta k + available.card ≤ e + positionLoad G available (p.getVert k)) :
    (∑ k ∈ positions, delta k) + positions.card*available.card ≤
      positions.card*e + (q+3)*available.card := by
  have hs := Finset.sum_le_sum hbudget
  have ht := total_position_load_le p q hp available positions hpositions
  have he : (∑ k ∈ positions, delta k) + positions.card*available.card ≤
      positions.card*e + ∑ k ∈ positions, positionLoad G available (p.getVert k) := by
    simpa [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Nat.mul_comm] using hs
  exact he.trans (Nat.add_le_add_left ht _)

theorem one_extra_edge_full_availability_mass
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (hp : p.length ≤ G.dist u v + 1)
    (available : Finset V) (positions : Finset ℕ)
    (hpositions : ∀ k ∈ positions, k ≤ p.length)
    (delta : ℕ → ℕ)
    (hbudget : ∀ k ∈ positions,
      delta k + available.card ≤ available.card + positionLoad G available (p.getVert k)) :
    (∑ k ∈ positions, delta k) ≤ 4*available.card := by
  have h := near_geodesic_carrier_mass p 1 hp available positions hpositions delta available.card hbudget
  omega

end HirschPortalDebt
end
theorem solution {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {u v : V} (p : G.Walk u v) (q : ℕ) (hp : p.length ≤ G.dist u v + q)
    (available : Finset V) (positions : Finset ℕ)
    (hpositions : ∀ k ∈ positions, k ≤ p.length) (delta : ℕ → ℕ) (e : ℕ)
    (hbudget : ∀ k ∈ positions, delta k + available.card ≤ e +
      (available.filter (fun z => z = p.getVert k ∨ G.Adj z (p.getVert k))).card) :
    (∑ k ∈ positions, delta k) + positions.card * available.card ≤
      positions.card * e + (q+3)*available.card := by
  classical
  apply HirschPortalDebt.near_geodesic_carrier_mass p q hp available positions hpositions delta e
  intro k hk
  simpa only [HirschPortalDebt.positionLoad, HirschPortalDebt.Contact] using hbudget k hk
