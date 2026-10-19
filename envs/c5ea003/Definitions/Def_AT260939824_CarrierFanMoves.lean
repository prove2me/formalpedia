-- Prove2me | Definitions.Def_AT260939824_CarrierFanMoves
-- name    : AT260939824_CarrierFanMoves
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T02:51:13.065685+00:00
-- url     : https://prove2.me/theorems/d88c1af5-fcd4-4d58-a67f-7cfcd0ae2626
-- title:
--   Fan rows inside a relation polygon
-- statement:
--   For a relation cell based at a carrier vertex $c$, the lower row consists of consecutive vertices on its $m$-edge lower boundary. The fan triangles have the common upper-left vertex and successive lower edges; one upper triangle completes the polygon. The selected row interfaces connect the lower boundary to the three-edge upper boundary with a vertex budget of $m+2$.
--
--   They relate the combinatorial relation move to actual permitted carrier faces.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (2026), Section(s) 4; https://arxiv.org/abs/2609.39824v1. This item is auxiliary infrastructure of the accompanying formalization, not a claim that each implementation definition is separately numbered in the paper. Original Lean module AbelianTargets/CarrierFanMoves.lean, selected declaration lines 7-9, 11-15, 17-19, 21-25, 27-30, 32-35, 37-50, 52-103; SHA-256 60724a0dcdeb8872c284eadf59a499c9b8322b12a735a41b0999c58a5a452c51. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_CarrierCellRealization
import Definitions.Def_AT260939824_CarrierTriangulation
import Definitions.Def_AT260939824_CompressedWords
import Definitions.Def_AT260939824_DigitPathRealization
import Definitions.Def_AT260939824_IntervalCarriers
import Definitions.Def_AT260939824_TriangleRowMoves
import Init
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Group.Conj
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Data.Int.Interval
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false

/-! # Actual presentation polygons collapse by bounded fan row moves -/

namespace AbelianTargets.IntervalCarriers

def lowerRow (m : ℕ) (c : Vertex) (n : ℕ) : ℕ → List Vertex
  | 0 => [lowerVertex m c.1 c.2 n]
  | k+1 => lowerVertex m c.1 c.2 n :: lowerRow m c (n+1) k

@[simp] theorem lowerRow_length (m : ℕ) (c : Vertex) (n k : ℕ) :
    (lowerRow m c n k).length = k+1 := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => simp only [lowerRow,List.length_cons,ih]

theorem lowerRow_head (m : ℕ) (c : Vertex) (n k : ℕ) :
    ∃ tail, lowerRow m c n k = lowerVertex m c.1 c.2 n :: tail := by
  cases k <;> exact ⟨_,rfl⟩

theorem lowerRow_of_pos (m : ℕ) (c : Vertex) (n k : ℕ) (hk : 1 ≤ k) :
    lowerRow m c n k = lowerVertex m c.1 c.2 n :: lowerRow m c (n+1) (k-1) := by
  cases k with
  | zero => omega
  | succ k => rfl

theorem lowerTriangle_face {m K n : ℕ} {A B : ℤ} {c : Vertex}
    (hc : c ∈ carrierCells m K A B) (hn : n < m) :
    CarrierFace m K A B {upperLeft c.1 c.2,lowerVertex m c.1 c.2 n,lowerVertex m c.1 c.2 (n+1)} :=
  Or.inr (Or.inr ⟨lowerTriangle m c n,mem_carrierTriangles_lower hc hn,Finset.Subset.refl _⟩)

theorem upperTriangle_face {m K : ℕ} {A B : ℤ} {c : Vertex}
    (hc : c ∈ carrierCells m K A B) :
    CarrierFace m K A B {upperLeft c.1 c.2,lowerVertex m c.1 c.2 m,upperRight m c.1 c.2} :=
  Or.inr (Or.inr ⟨upperTriangle m c,mem_carrierTriangles_upper hc,Finset.Subset.refl _⟩)

theorem lowerRow_fan {m K n k : ℕ} {A B : ℤ} {c : Vertex}
    (hc : c ∈ carrierCells m K A B) (hn : n+k ≤ m) :
    FanChain (CarrierFace m K A B) (upperLeft c.1 c.2)
      (lowerRow m c n k) (lowerVertex m c.1 c.2 (n+k)) := by
  induction k generalizing n with
  | zero => exact .single _
  | succ k ih =>
      have h := ih (n := n+1) (by omega)
      have heq : n+1+k = n+(k+1) := by omega
      rw [heq] at h
      obtain ⟨tail,htail⟩ := lowerRow_head m c (n+1) k
      rw [htail] at h
      rw [lowerRow,htail]
      exact .cons (lowerTriangle_face hc (by omega)) h

/-- The lower `m`-edge side and the three-edge upper side are joined by
actual fan triangle moves. Every intermediate vertex row has at most
`m+2` entries. -/
theorem presentation_polygon_rows {m K : ℕ} {A B : ℤ} {c : Vertex}
    (hm : 2 ≤ m) (hc : c ∈ carrierCells m K A B) :
    BoundedTriangleRows (CarrierFace m K A B) (m+2)
      (lowerRow m c 0 m)
      [lowerVertex m c.1 c.2 0,upperLeft c.1 c.2,
        upperRight m c.1 c.2,lowerVertex m c.1 c.2 m] := by
  let L₀ := lowerVertex m c.1 c.2 0
  let L₁ := lowerVertex m c.1 c.2 1
  let Lₘ := lowerVertex m c.1 c.2 m
  let U := upperLeft c.1 c.2
  let V := upperRight m c.1 c.2
  obtain ⟨tail,htail⟩ := lowerRow_head m c 1 (m-1)
  have hrow : lowerRow m c 0 m = L₀::L₁::tail := by
    rw [lowerRow_of_pos m c 0 m (by omega),htail]
  have hlength : tail.length+2 = m+1 := by
    have h := lowerRow_length m c 0 m
    rw [hrow] at h
    simpa only [List.length_cons] using h
  have hf₀ : CarrierFace m K A B {L₀,U,L₁} := by
    have h := lowerTriangle_face hc (show 0 < m by omega)
    simpa only [L₀,L₁,U,Finset.insert_comm] using h
  have h₁ : BoundedTriangleRows (CarrierFace m K A B) (m+2)
      (L₀::L₁::tail) (L₀::U::L₁::tail) := by
    have h := BoundedTriangleRows.triangle (B := m+2) L₀ U L₁ hf₀ [] tail
      (by simp only [List.length_append,List.length_cons,List.length_nil]; omega)
      (by simp only [List.length_append,List.length_cons,List.length_nil]; omega)
    simpa only [List.nil_append,List.cons_append,List.nil_append] using h.symm
  have hfan := lowerRow_fan (n := 1) (k := m-1) hc (by omega)
  have heq : 1+(m-1) = m := by omega
  rw [heq,htail] at hfan
  have h₂ : BoundedTriangleRows (CarrierFace m K A B) (m+2)
      (L₀::U::L₁::tail) [L₀,U,Lₘ] := by
    have h := hfan.contract (B := m+1) (by simp only [List.length_cons]; omega)
    have h' := h.context [L₀] []
    simpa only [L₁,Lₘ,U,List.length_cons,List.length_nil,List.nil_append,
      List.cons_append,List.append_nil,Nat.add_zero] using h'
  have hf₁ : CarrierFace m K A B {U,V,Lₘ} := by
    have h := upperTriangle_face hc
    change CarrierFace m K A B {U,Lₘ,V} at h
    rw [Finset.pair_comm Lₘ V] at h
    exact h
  have h₃ : BoundedTriangleRows (CarrierFace m K A B) (m+2)
      [L₀,U,Lₘ] [L₀,U,V,Lₘ] := by
    have h := BoundedTriangleRows.triangle (B := m+2) U V Lₘ hf₁ [L₀] []
      (by simp only [List.length_append,List.length_cons,List.length_nil]; omega)
      (by simp only [List.length_append,List.length_cons,List.length_nil]; omega)
    simpa only [List.nil_append,List.cons_append,List.append_nil] using h.symm
  rw [hrow]
  exact h₁.trans (h₂.trans h₃)

end AbelianTargets.IntervalCarriers


