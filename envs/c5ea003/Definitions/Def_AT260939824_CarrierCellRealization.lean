-- Prove2me | Definitions.Def_AT260939824_CarrierCellRealization
-- name    : AT260939824_CarrierCellRealization
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T02:45:27.360235+00:00
-- url     : https://prove2.me/theorems/ead77a94-211d-4de5-b911-78b54ee0255d
-- title:
--   Word-path casts and concatenation splitting
-- statement:
--   A word path in the interval-carrier graph records a sequence of labelled edges from a source vertex to a target vertex. Equality of its label words transports the same path without changing its vertices. A path labelled by a concatenation $ab$ splits at an intermediate vertex into an $a$-path followed by a $b$-path.
--
--   This interface makes word identities usable with the literal edge paths and their vertex lists.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (2026), Section(s) 4; https://arxiv.org/abs/2609.39824v1. This item is auxiliary infrastructure of the accompanying formalization, not a claim that each implementation definition is separately numbered in the paper. Original Lean module AbelianTargets/CarrierCellRealization.lean, selected declaration lines 7-9, 17-18, 20-23, 25-35; SHA-256 41f412bb6aa71dbcfb2da3f2e2498f978901801889cf9db0fa197d7cd93ad6c5. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_CompressedWords
import Definitions.Def_AT260939824_DigitPathRealization
import Definitions.Def_AT260939824_IntervalCarriers
import Init
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Group.Conj
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false

/-! # Every digital relation move uses a cell of the literal finite carrier -/

namespace AbelianTargets.IntervalCarriers

theorem WordPath.start_mem_vertices {m : ℕ} {x z : Vertex} {w : List BSLetter}
    (p : WordPath m x w z) : x ∈ p.vertices := by
  cases p <;> simp [WordPath.vertices]



def WordPath.castWord {m : ℕ} {x z : Vertex} {w u : List BSLetter}
    (p : WordPath m x w z) (hw : w = u) : WordPath m x u z := hw ▸ p

@[simp] theorem WordPath.vertices_castWord {m : ℕ} {x z : Vertex} {w u : List BSLetter}
    (p : WordPath m x w z) (hw : w = u) : (p.castWord hw).vertices = p.vertices := by
  cases hw
  rfl

theorem WordPath.split {m : ℕ} {x z : Vertex} (a b : List BSLetter)
    (p : WordPath m x (a++b) z) :
    ∃ (y : Vertex) (u : WordPath m x a y) (v : WordPath m y b z),
      p.vertices = (u.append v).vertices := by
  induction a generalizing x with
  | nil => exact ⟨x,.nil x,p,rfl⟩
  | cons s a ih =>
      cases p with
      | cons h p =>
          obtain ⟨y,u,v,heq⟩ := ih p
          exact ⟨y,.cons h u,v,by simp only [WordPath.vertices,WordPath.append,heq]⟩





end AbelianTargets.IntervalCarriers


