-- Prove2me | Definitions.Def_AT260939824_CanonicalRows
-- name    : AT260939824_CanonicalRows
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T02:59:13.835222+00:00
-- url     : https://prove2.me/theorems/fa471d5f-756f-4435-a1f4-f9a0e66e96a5
-- title:
--   Fixed-slot realizations of valid vertex rows
-- statement:
--   Let $\iota:V\to E$ realize vertices in a normed real space. A finite row with specified initial and terminal vertices is evaluated at natural-number slots, with terminal padding when necessary. A row of length $n+2$ determines a based row with those endpoints.
--
--   Validity, endpoint, and edge-bound lemmas preserve the row's allowable-face structure. These definitions give a common geometric representation for combinatorial row moves.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (2026), Section(s) 4; https://arxiv.org/abs/2609.39824v1. This item is auxiliary infrastructure of the accompanying formalization, not a claim that each implementation definition is separately numbered in the paper. Original Lean module AbelianTargets/CanonicalRows.lean, selected declaration lines 9-25, 27-57, 59-63, 65-76, 78-83, 91, 93-99, 101-104, 106-111, 113-121; SHA-256 36a55ae27f16e13e338df30cbabac1625a5a3ed436d6a655186270c72c1ff789. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_CarrierCellRealization
import Definitions.Def_AT260939824_CarrierFanMoves
import Definitions.Def_AT260939824_CompressedWords
import Definitions.Def_AT260939824_DigitPathRealization
import Definitions.Def_AT260939824_FixedSlotInterpolation
import Definitions.Def_AT260939824_FixedSlotPadding
import Definitions.Def_AT260939824_IntervalCarriers
import Definitions.Def_AT260939824_PauseSliding
import Definitions.Def_AT260939824_RelativePathContraction
import Definitions.Def_AT260939824_RowValidity
import Definitions.Def_AT260939824_WordPathHelpers
import Init
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Group.Conj
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Data.Int.Interval
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Chain
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Homotopy.Path
import Mathlib.Topology.MetricSpace.Lipschitz

set_option autoImplicit false

/-! # Canonical endpoint-padded rows and their exact fixed-slot endpoints -/

namespace AbelianTargets

variable {V : Type*} [DecidableEq V] {Face : Finset V → Prop}

theorem FixedRowMoves.valid_iff {w u : List V} (h : FixedRowMoves Face w u)
    (hd : FaceDownward Face) : ValidRow Face w ↔ ValidRow Face u := by
  induction h with
  | refl w => rfl
  | replace a b b' c hf p s =>
      have hf₀ : Face {a,b,c} := hd hf (by
        intro v hv
        simp only [Finset.mem_insert,Finset.mem_singleton] at hv ⊢
        obtain rfl | rfl | rfl := hv <;> simp)
      have hf₁ : Face {a,b',c} := hd hf (by
        intro v hv
        simp only [Finset.mem_insert,Finset.mem_singleton] at hv ⊢
        obtain rfl | rfl | rfl := hv <;> simp)
      exact (validRow_triangle_iff hd a b c hf₀ p s).trans
        (validRow_triangle_iff hd a b' c hf₁ p s).symm
  | symm h ih => exact ih.symm
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

theorem ValidRow.pad {w : List V} (h : ValidRow Face w) {z : V}
    (hz : w.getLast? = some z) (N : ℕ) : ValidRow Face (padRow N z w) := by
  have hzmem : z ∈ w := List.mem_of_mem_getLast? (by simp [hz])
  have hzface := h.vertices z hzmem
  have hzz : Face {z,z} := by simpa using hzface
  have hrep : ∀ k, List.IsChain (fun a b => Face {a,b}) (List.replicate k z) := by
    intro k
    induction k with
    | zero => exact .nil
    | succ k ih =>
      cases k with
      | zero => exact .singleton z
      | succ k => exact .cons_cons hzz ih
  constructor
  · apply h.chain.append (hrep _)
    intro a ha b hb
    have ha' : a = z := (by simpa only [hz,Option.mem_some_iff] using ha : z = a).symm
    have hb' : b = z := by
      cases hk : N-w.length with
      | zero => simp [hk] at hb
      | succ k =>
        have hb'' : z = b := by
          simpa only [hk,List.replicate_succ,List.head?_cons,Option.mem_some_iff] using hb
        exact hb''.symm
    simpa only [ha',hb'] using hzz
  · intro v hv
    simp only [padRow,List.mem_append] at hv
    obtain hv | hv := hv
    · exact h.vertices v hv
    · have hv' : v = z := (List.mem_replicate.mp hv).2
      simpa only [hv'] using hzface

theorem padRow_head {w : List V} {x z : V} (hx : w.head? = some x) (N : ℕ) :
    (padRow N z w).head? = some x := by
  cases w with
  | nil => simp at hx
  | cons a w => simpa only [padRow,List.cons_append,List.head?_cons] using hx

theorem padRow_last {w : List V} {z : V} (hz : w.getLast? = some z) (N : ℕ) :
    (padRow N z w).getLast? = some z := by
  unfold padRow
  cases hk : N-w.length with
  | zero => simpa only [List.replicate_zero,List.append_nil] using hz
  | succ k =>
    have hl : (z :: List.replicate k z).getLast? = some z := by
      clear hk
      induction k with
      | zero => rfl
      | succ k ih => simpa only [List.replicate_succ,List.getLast?_cons_cons] using ih
    simpa only [List.replicate_succ,List.getLast?_append_cons] using hl

theorem ValidRow.edge_getD {w : List V} (h : ValidRow Face w) (z : V)
    (j : ℕ) (hj : j+1 < w.length) : Face {w.getD j z,w.getD (j+1) z} := by
  have h' := h.chain.getElem j hj
  have hj₀ : j < w.length := by omega
  simpa only [← List.getElem_eq_getD (h := hj₀) z,
    ← List.getElem_eq_getD (h := hj) z] using h'

namespace FixedSlots

open scoped NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def listRow (ι : V → E) (z : V) (w : List V) : ℕ → E := fun j => ι (w.getD j z)

theorem listRow_zero (ι : V → E) {x z : V} {w : List V}
    (hx : w.head? = some x) : listRow ι z w 0 = ι x := by
  cases w with
  | nil => simp at hx
  | cons a w =>
      have ha : a = x := Option.some.inj hx
      simp only [listRow,List.getD_cons_zero,ha]

theorem listRow_last (ι : V → E) {n : ℕ} {z : V} {w : List V}
    (hlen : w.length = n+2) (hz : w.getLast? = some z) : listRow ι z w (n+1) = ι z := by
  have hi : n+1 = w.length-1 := by omega
  simp only [listRow,List.getD_eq_getElem?_getD,hi,← List.getLast?_eq_getElem?,hz,Option.getD_some]

def canonicalRow (ι : V → E) (n : ℕ) (x z : V) (w : List V)
    (hx : w.head? = some x) (hz : w.getLast? = some z) (hlen : w.length = n+2) :
    BasedRow n (ι x) (ι z) where
  vertices := listRow ι z w
  source := listRow_zero ι hx
  target := listRow_last ι hlen hz

theorem canonicalRow_edges (ι : V → E) {n : ℕ} {x z : V} {w : List V}
    (hx : w.head? = some x) (hz : w.getLast? = some z) (hlen : w.length = n+2)
    (hvalid : ValidRow Face w) (Δ : ℝ≥0)
    (hedge : ∀ a b, Face {a,b} → dist (ι a) (ι b) ≤ Δ) :
    ∀ j ≤ n, dist ((canonicalRow ι n x z w hx hz hlen).vertices j)
      ((canonicalRow ι n x z w hx hz hlen).vertices (j+1)) ≤ Δ := by
  intro j hj
  apply hedge
  exact hvalid.edge_getD z j (by omega)

end FixedSlots

end AbelianTargets


