-- Prove2me | Definitions.Def_AT260939824_WordPathHelpers
-- name    : AT260939824_WordPathHelpers
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T02:51:55.16591+00:00
-- url     : https://prove2.me/theorems/5393930a-1a1d-4b74-b5b3-04d661df882c
-- title:
--   Uniqueness and vertex lists of presentation-word paths
-- statement:
--   For the presentation graph with base $m\in\mathbb N$, a fixed letter and starting vertex determine at most one endpoint. Consequently a word $w$ and initial vertex determine both the endpoint and full vertex list of any word path realizing $w$. For such a path $P$,
--   $$|\operatorname{vertices}(P)|=|w|+1,$$
--   so the vertex list is nonempty. If $P$ and $Q$ are composable word paths, then
--   $$\operatorname{vertices}(P*Q)=
--   \operatorname{dropLast}(\operatorname{vertices}(P))\,\mathbin{+\!\!+}\,
--   \operatorname{vertices}(Q).$$
--   This concatenation formula includes the common endpoint once and is used to move between word deformations and finite vertex rows.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Sections 2–7, supporting construction for Theorem 1.4 and Proposition 7.1; https://arxiv.org/html/2609.39824v1. Formalization-specific infrastructure in the import closure; individual helper assertions are not represented as separately numbered paper theorems. Original Lean module AbelianTargets/WordPathHelpers.lean, selected declaration lines 13-23, 25-34, 36-46, 48-52, 54-60, 62-69; SHA-256 f0af8ece0b3d3ac110e16e5f257352425bfdde6cc5426e2fb9a621878b5bc909. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

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

/-!
# Determinism and exact vertex rows of directed carrier word paths

The elementary directed steps determine their endpoint. Consequently an
edge word has a unique literal vertex row from a specified start, and
concatenation removes exactly one copy of the shared endpoint.
-/

namespace AbelianTargets.IntervalCarriers

theorem LetterStep.unique {m : ℕ} {s : BSLetter} {x y z : Vertex}
    (h : LetterStep m s x y) (h' : LetterStep m s x z) : y = z := by
  cases s with
  | a => exact h.trans h'.symm
  | t => exact h.trans h'.symm
  | tInv =>
      have hy₁ := congrArg Prod.fst h
      have hy₂ := congrArg Prod.snd h
      have hz₁ := congrArg Prod.fst h'
      have hz₂ := congrArg Prod.snd h'
      apply Prod.ext <;> dsimp [LetterStep,VerticalStep] at * <;> omega

theorem WordPath.endpoint_eq {m : ℕ} {x y z : Vertex} {w : List BSLetter}
    (p : WordPath m x w y) (q : WordPath m x w z) : y = z := by
  induction p generalizing z with
  | nil x => cases q; rfl
  | @cons s x u y w h p ih =>
      cases q with
      | @cons _ _ v _ _ h' q =>
          have huv := h.unique h'
          subst v
          exact ih q

theorem WordPath.vertices_eq {m : ℕ} {x y z : Vertex} {w : List BSLetter}
    (p : WordPath m x w y) (q : WordPath m x w z) : p.vertices = q.vertices := by
  induction p generalizing z with
  | nil x => cases q; rfl
  | @cons s x u y w h p ih =>
      cases q with
      | @cons _ _ v _ _ h' q =>
          have huv := h.unique h'
          subst v
          simp only [WordPath.vertices]
          exact congrArg (List.cons x) (ih q)

@[simp] theorem WordPath.vertices_length {m : ℕ} {x y : Vertex} {w : List BSLetter}
    (p : WordPath m x w y) : p.vertices.length = w.length+1 := by
  induction p with
  | nil x => rfl
  | cons h p ih => simp only [WordPath.vertices,List.length_cons,ih]

theorem WordPath.vertices_ne_nil {m : ℕ} {x y : Vertex} {w : List BSLetter}
    (p : WordPath m x w y) : p.vertices ≠ [] := by
  intro h
  have hh := p.vertices_length
  rw [h] at hh
  simp only [List.length_nil] at hh
  omega

@[simp] theorem WordPath.vertices_append {m : ℕ} {x y z : Vertex} {w u : List BSLetter}
    (p : WordPath m x w y) (q : WordPath m y u z) :
    (p.append q).vertices = p.vertices.dropLast ++ q.vertices := by
  induction p with
  | nil x => rfl
  | @cons s x v y w h p ih =>
      simp only [WordPath.append,WordPath.vertices,ih]
      rw [List.dropLast_cons_of_ne_nil p.vertices_ne_nil,List.cons_append]

end AbelianTargets.IntervalCarriers


