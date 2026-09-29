-- Prove2me | solution 1 for TriangularForest.IsTriangularForest.mono
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-16T06:50:29.185095+00:00
-- url     : https://prove2.me/submissions/d4c5249a-ccda-4f92-a2d1-0ce06fea447f

/-
# `TriangularForest.IsTriangularForest.mono`
Target `739deed8` (Open, not deprecated at draft time; re-read live immediately before submitting).

ORDINARY PROOF — chain screened: the bundle's `Definitions.` closure has NO `Theorems.` import,
so no `sorryAx` and no axiom audit.

    IsTriangularForest G = ∀ ⦃v⦄ (c : G.Walk v v), c.IsCycle → c.length = 3

Claim: `H ≤ G → IsTriangularForest G → IsTriangularForest H`.

A cycle in the SMALLER graph is still a cycle in the larger one, and mapping does not change its
length. So the hypothesis applies to the image and transfers back.

PROBED, NOT GUESSED — read out of the vendored Mathlib source:
  * `Walk.mapLe h p` is an ABBREV for `p.map (Hom.ofLE h)` (`Walk/Maps.lean:129`), so lemmas
    about `map` apply to it directly.
  * `Walk.mapLe_isCycle (h : G ≤ G') {p : G.Walk u u} : (p.mapLe h).IsCycle ↔ p.IsCycle`
    (`Paths.lean:901`), `@[simp]`, with `alias ⟨IsCycle.of_mapLe, IsCycle.mapLe⟩`.
    COMPILE CORRECTION: `hc.mapLe` does NOT work — `h` is an EXPLICIT argument preceding the
    implicit walk, so dot-notation left it unapplied (`fun h => IsCycle.mapLe h hc`).
    Use the iff directly: `(Walk.mapLe_isCycle hle).mpr hc`.
  * `Walk.length_map : (p.map f).length = p.length` (`Maps.lean:87`), `@[simp]`.
    COMPILE CORRECTION: being `@[simp]` is not enough. `Walk.mapLe` is an `abbrev`
    (`Maps.lean:129`) and simp did not see through it, leaving
    `(Walk.mapLe hle c).length = 3` against a goal of `c.length = 3`. Reducible does NOT mean
    simp unfolds it — `simp [Walk.mapLe]` must name it. There is no `length_mapLe` lemma.

BINDERS — four rejections on this target, all the same mistake, and the message states the
expected type verbatim:

    has type     ∀ {V} {G H} [Fintype V] [DecidableRel G.Adj] [DecidableEq V], H ≤ G → ...
    but expected ∀ {V} {G H},                                                  H ≤ G → ...

NO instances at all. The bundle declares `variable [Fintype V] [DecidableRel G.Adj]` in a LATER
section than this statement, so anything written against the file as a whole inherits them.
-/
import Mathlib
import Definitions.Def_Logic_TriangularForest_Defs

set_option autoImplicit false
set_option maxHeartbeats 400000

open SimpleGraph TriangularForest in
/-- **The target, verbatim.** -/
theorem solution {V : Type*} {G H : SimpleGraph V} (hle : H ≤ G)
    (hG : IsTriangularForest G) : IsTriangularForest H := by
  intro v c hc
  -- the same cycle, viewed in the larger graph
  -- write the map form OUTRIGHT: `mapLe` is an abbrev and this Mathlib revision has a
  -- transparency problem around it (see the `backward.isDefEq.respectTransparency` guard
  -- on its neighbour in Walk/Maps.lean), so simp will not reach `length_map` through it
  have hcyc : (c.map (Hom.ofLE hle)).IsCycle := (Walk.mapLe_isCycle hle).mpr hc
  have hmap := hG (c.map (Hom.ofLE hle)) hcyc
  rwa [Walk.length_map] at hmap
