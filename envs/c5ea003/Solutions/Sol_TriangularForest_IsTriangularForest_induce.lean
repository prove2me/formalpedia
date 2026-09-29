-- Prove2me | solution 1 for TriangularForest.IsTriangularForest.induce
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-16T07:51:50.31302+00:00
-- url     : https://prove2.me/submissions/9bab1ac6-8759-4439-bb93-f1a41adca4e8

/-
# `TriangularForest.IsTriangularForest.induce`
Target `88f09dd9` (Open; re-read live immediately before submitting).

ORDINARY PROOF — screen CLEAN (exit 0). Gift-safe under the corrected check (which now excludes
Definition-bundle nodes from the premise count).

BINDERS — expected type, verbatim from the WA (four of them, all identical):

    has type     ∀ {V} {G} [Fintype V] [DecidableRel G.Adj] [DecidableEq V] (s : Set V),
                   IsTriangularForest G → IsTriangularForest (SimpleGraph.induce s G)
    but expected ∀ {V} {G} (s : Set V),
                   IsTriangularForest G → IsTriangularForest (SimpleGraph.induce s G)

NO instances at all — the identical trap that sank `739deed8 mono` four times: the bundle declares
`[Fintype V] [DecidableRel G.Adj]` in a LATER section than this statement, so anything written
against the file as a whole inherits them.

MATHS. Exactly the `mono` argument with a different transport. A cycle in `G.induce s` pushes
forward along the induced-subgraph EMBEDDING into `G`; an embedding is injective, so the image is
still a cycle, and mapping does not change length. The hypothesis applies to the image and the
length transfers back.

PROBED, NOT GUESSED — read out of source:
  * `Walk.map_isCycle_iff_of_injective {p : G.Walk u u} (hinj : Function.Injective f) :
       (p.map f).IsCycle ↔ p.IsCycle` (Paths.lean:879).
    It carries `alias ⟨_, IsCycle.map⟩`. DELIBERATELY NOT USED as `hc.map hinj`: that is the same
    shape as `hc.mapLe`, which mis-elaborated earlier today because the explicit hypothesis precedes
    the implicit walk, leaving it unapplied. The iff is used directly, as in the accepted `mono`.
  * `Embedding.induce (s : Set V) : G.induce s ↪g G` — confirmed by four call sites
    (Walk/Maps.lean:218, Connected.lean:689/698, Clique.lean:360).
  * `Walk.length_map : (p.map f).length = p.length` (Maps.lean:87) — already used in the accepted
    `mono` proof, where simp could NOT reach it through the `mapLe` abbrev. Here the map form is
    written outright, so no abbrev stands in the way.
-/
import Mathlib
import Definitions.Def_Logic_TriangularForest_Defs

set_option autoImplicit false
set_option maxHeartbeats 400000

open SimpleGraph TriangularForest


open SimpleGraph TriangularForest in
/-- **The target, verbatim.** -/
theorem solution {V : Type*} {G : SimpleGraph V} (s : Set V)
    (hG : IsTriangularForest G) : IsTriangularForest (G.induce s) := by
  intro v c hc
  -- the induced-subgraph embedding is injective, so the image of a cycle is a cycle
  have hinj : Function.Injective (Embedding.induce (G := G) s).toHom :=
    (Embedding.induce (G := G) s).injective
  have hmap := hG (c.map (Embedding.induce (G := G) s).toHom)
                  ((Walk.map_isCycle_iff_of_injective hinj).mpr hc)
  -- mapping preserves length, so transfer the answer back
  rwa [Walk.length_map] at hmap
