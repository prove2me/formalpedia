-- Prove2me | Definitions.Def_AT260939824_FixedSlotPadding
-- name    : AT260939824_FixedSlotPadding
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T02:58:20.550264+00:00
-- url     : https://prove2.me/theorems/4f49ed63-950b-4403-8b0b-871079b53cd0
-- title:
--   Canonical endpoint padding of row chains
-- statement:
--   A finite row with a specified terminal vertex is padded by repeated terminal vertices to a common length $N$. Triangle moves become equal-slot replacements followed by transport of a pause through the remaining tail, and pause deletions use the same transport. Consequently every bounded triangle-row certificate whose budget is at most $N$ induces a chain of common-slot moves between the canonically padded endpoint rows.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Sections 2-7; https://arxiv.org/html/2609.39824v1. Formalization-specific infrastructure in the import closure of Theorem 1.4 and Proposition 7.1; individual helper assertions are not represented as separately numbered paper theorems. Original Lean module AbelianTargets/FixedSlotPadding.lean, selected declaration lines 17-18, 20-23, 25-59, 61-84, 86-106; SHA-256 72cac76e9d282ce2250604808b8f57fdf7e53ee8851a8781f4de100d1934f3db. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_CarrierCellRealization
import Definitions.Def_AT260939824_CarrierFanMoves
import Definitions.Def_AT260939824_CompressedWords
import Definitions.Def_AT260939824_ContextualCarrierRows
import Definitions.Def_AT260939824_DigitPathRealization
import Definitions.Def_AT260939824_FixedSlotInterpolation
import Definitions.Def_AT260939824_IntervalCarriers
import Definitions.Def_AT260939824_PauseSliding
import Definitions.Def_AT260939824_RelativePathContraction
import Definitions.Def_AT260939824_RowValidity
import Definitions.Def_AT260939824_TriangleRowMoves
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

/-!
# Canonical common-slot padding of every bounded cellular row chain

Each row is padded only at its endpoint. A triangle collapse becomes
one equal-slot local replacement followed by pause transport through
the entire remaining tail. A pause deletion is exactly pause transport.
The reverse moves are their inverse chains, so expansions automatically
use the pauses supplied by the common budget.
-/

namespace AbelianTargets

variable {V : Type*} [DecidableEq V] {Face : Finset V → Prop}

def padRow (N : ℕ) (z : V) (w : List V) : List V :=
  w ++ List.replicate (N-w.length) z

theorem padRow_length {N : ℕ} {z : V} {w : List V} (hw : w.length ≤ N) :
    (padRow N z w).length = N := by
  simp only [padRow,List.length_append,List.length_replicate]
  omega

theorem padded_triangle_move (hd : FaceDownward Face) (N : ℕ) (z a b c : V)
    (hf : Face {a,b,c}) (p s : List V)
    (hv : ValidRow Face (p++[a,b,c]++s))
    (hz : (p++[a,b,c]++s).getLast? = some z)
    (hlen : (p++[a,b,c]++s).length ≤ N) :
    FixedRowMoves Face (padRow N z (p++[a,b,c]++s))
      (padRow N z (p++[a,c]++s)) := by
  let k := N-(p++[a,b,c]++s).length
  have hk : N-(p++[a,c]++s).length = k+1 := by
    dsimp [k]
    simp only [List.length_append,List.length_cons,List.length_nil] at hlen ⊢
    omega
  have hf' : Face {a,b,a,c} := by
    have heq : ({a,b,a,c} : Finset V) = {a,b,c} := by ext v; simp [or_assoc,or_left_comm,or_comm]
    rw [heq]
    exact hf
  have hshort := (validRow_triangle_iff hd a b c hf p s).mp hv
  have hchain : List.IsChain (fun a b => Face {a,b}) (a::c::s) := by
    have hc := hshort.chain
    simp only [List.append_assoc,List.cons_append,List.nil_append] at hc
    exact (List.isChain_split.mp hc).2
  have hlast : (a::c::s).getLast? = some z := by
    simpa only [List.append_assoc,List.cons_append,List.nil_append,
      List.getLast?_append_cons,List.getLast?_cons_cons] using hz
  have htail := edgeRow_of_chain_last hchain hlast
  have h₁ : FixedRowMoves Face
      (p++[a,b,c]++s++List.replicate k z)
      (p++[a,a,c]++s++List.replicate k z) := by
    simpa only [List.append_assoc] using FixedRowMoves.replace a b a c hf' p (s++List.replicate k z)
  have h₂ := htail.slide_pause_to_end.context p (List.replicate k z)
  have h₂' : FixedRowMoves Face
      (p++[a,a,c]++s++List.replicate k z)
      (p++[a,c]++s++List.replicate (k+1) z) := by
    simpa only [List.append_assoc,List.cons_append,List.nil_append,List.replicate_succ] using h₂
  simpa only [padRow,k,hk] using h₁.trans h₂'

theorem padded_pause_move (N : ℕ) (z a : V) (p s : List V)
    (hv : ValidRow Face (p++[a,a]++s))
    (hz : (p++[a,a]++s).getLast? = some z)
    (hlen : (p++[a,a]++s).length ≤ N) :
    FixedRowMoves Face (padRow N z (p++[a,a]++s))
      (padRow N z (p++[a]++s)) := by
  let k := N-(p++[a,a]++s).length
  have hk : N-(p++[a]++s).length = k+1 := by
    dsimp [k]
    simp only [List.length_append,List.length_cons,List.length_nil] at hlen ⊢
    omega
  have hshort := (validRow_pause_iff a p s).mp hv
  have hchain : List.IsChain (fun a b => Face {a,b}) (a::s) := by
    have hc := hshort.chain
    simp only [List.append_assoc,List.cons_append,List.nil_append] at hc
    exact (List.isChain_split.mp hc).2
  have hlast : (a::s).getLast? = some z := by
    simpa only [List.append_assoc,List.cons_append,List.nil_append,
      List.getLast?_append_cons,List.getLast?_cons_cons] using hz
  have h := (edgeRow_of_chain_last hchain hlast).slide_pause_to_end.context p (List.replicate k z)
  change FixedRowMoves Face ((p++[a,a]++s)++List.replicate k z)
    ((p++[a]++s)++List.replicate (N-(p++[a]++s).length) z)
  rw [hk]
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.replicate_succ] using h

/-- Complete bounded-row to common-slot adapter. The canonical padding
is the same at every endpoint and every stage; no new homotopy axiom is
used. -/
theorem BoundedTriangleRows.toFixedRows {B N : ℕ} {w u : List V}
    (h : BoundedTriangleRows Face B w u) (hd : FaceDownward Face) (hBN : B ≤ N)
    (z : V) : ValidRow Face w → w.getLast? = some z →
      FixedRowMoves Face (padRow N z w) (padRow N z u) := by
  induction h with
  | refl w hl => intro hv hz; exact .refl _
  | triangle a b c hf p s hw hu =>
      intro hv hz
      exact padded_triangle_move hd N z a b c hf p s hv hz (hw.trans hBN)
  | pause a p s hw hu =>
      intro hv hz
      exact padded_pause_move N z a p s hv hz (hw.trans hBN)
  | symm h ih =>
      intro hv hz
      exact (ih ((h.valid_iff hd).mpr hv) (h.last_eq.trans hz)).symm
  | trans h₁ h₂ ih₁ ih₂ =>
      intro hv hz
      exact (ih₁ hv hz).trans (ih₂ ((h₁.valid_iff hd).mp hv) (h₁.last_eq.symm.trans hz))

end AbelianTargets


