-- Prove2me | solution 1 for TriangularForest.exists_maxPath
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-16T08:00:09.759212+00:00
-- url     : https://prove2.me/submissions/e5c16eeb-6db9-4d03-acdb-82f77694507f

/-
# `TriangularForest.exists_maxPath`
Target `3756ac6d` (Open; re-read live immediately before submitting).

ORDINARY PROOF — screen CLEAN. Gift-SAFE under the corrected check (which excludes Definition-bundle
nodes from the premise count).

BINDERS — expected type, verbatim from a WA (four of them):

    ∀ {V : Type _} [Fintype V] [Nonempty V] (G : SimpleGraph V),
      ∃ a b p, p.IsPath ∧ ∀ (x y : V) (q : G.Walk x y), q.IsPath → q.length ≤ p.length

Instances ARE required here — unlike `induce`, which takes none. Same file, opposite answer, because
`Fintype V` is what makes a longest path exist at all.

MATHS. The lengths of paths form a set of naturals that is
  * NON-EMPTY — the trivial path at any vertex has length 0, and `[Nonempty V]` supplies a vertex;
  * BOUNDED — a path's support is duplicate-free, so its length is below `|V|`.
A non-empty bounded set of naturals attains its supremum, and the attaining path is the maximum.

PROBED, NOT GUESSED — each read out of source:
  * `SimpleGraph.Walk.IsPath.length_lt [Fintype V] (hp : p.IsPath) : p.length < Fintype.card V`
    (Paths.lean:381). Found by searching CONTENT (`IsPath.*length.*card`) after guessed names
    returned nothing.
  * `SimpleGraph.Walk.IsPath.nil : (nil : G.Walk u u).IsPath` (Paths.lean:184).
  * `Nat.sSup_mem {s : Set ℕ} (h₁ : s.Nonempty) (h₂ : BddAbove s) : sSup s ∈ s`
    (Data/Nat/Lattice.lean:149). Found only after dropping the namespace prefix from the search —
    inside `namespace Nat` the declaration reads `theorem sSup_mem`, with no `Nat.`.
  * `le_csSup` for the maximality direction.
-/
import Mathlib
import Definitions.Def_Logic_TriangularForest_Defs

set_option autoImplicit false
set_option maxHeartbeats 400000

open SimpleGraph TriangularForest


open SimpleGraph TriangularForest in
/-- **The target, verbatim.** -/
theorem solution {V : Type*} [Fintype V] [Nonempty V] (G : SimpleGraph V) :
    ∃ (a b : V) (p : G.Walk a b), p.IsPath ∧
      ∀ (x y : V) (q : G.Walk x y), q.IsPath → q.length ≤ p.length := by
  classical
  -- the set of lengths realised by paths of G
  set S : Set ℕ := {n | ∃ (a b : V) (p : G.Walk a b), p.IsPath ∧ p.length = n} with hSdef
  have hne : S.Nonempty := by
    obtain ⟨v⟩ := (inferInstance : Nonempty V)
    exact ⟨0, v, v, Walk.nil, Walk.IsPath.nil, rfl⟩
  have hbdd : BddAbove S := by
    refine ⟨Fintype.card V, ?_⟩
    rintro n ⟨a, b, p, hp, rfl⟩
    exact hp.length_lt.le
  -- a non-empty bounded set of naturals attains its supremum
  obtain ⟨a, b, p, hp, hlen⟩ := Nat.sSup_mem hne hbdd
  refine ⟨a, b, p, hp, ?_⟩
  intro x y q hq
  rw [hlen]
  exact le_csSup hbdd ⟨x, y, q, hq, rfl⟩
