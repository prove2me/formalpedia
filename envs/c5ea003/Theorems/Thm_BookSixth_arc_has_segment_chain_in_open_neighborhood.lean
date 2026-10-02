-- Prove2me | Theorems.Thm_BookSixth_arc_has_segment_chain_in_open_neighborhood
-- name    : BookSixth.arc_has_segment_chain_in_open_neighborhood
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-24T08:08:23.049985+00:00
-- url     : https://prove2.me/theorems/ace8b287-0a3c-47f6-8111-982a43d80098
-- title:
--   A continuous plane arc admits a finite segment chain in an open neighborhood
-- statement:
--   If the image of one selected continuous drawing arc lies in an open subset of the Euclidean plane, then the arc's two endpoint vertices are joined by a finite chain of straight segments, each contained in that open subset. This is a finite polygonal representation step only; it does not assert injectivity, loop erasure, preservation of the whole arc image, or any Euler or face-incidence count.
-- source:
--   Derived polygonal-representation child for the crossing-free plane drawing in Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), Chapter 45, Theorem 4, p. 317, https://doi.org/10.1007/978-3-662-57265-8_45. The construction uses the continuous preconnectedness of the arc image and finite chains of segments in an open neighborhood; injectivity, loop erasure, and planar counting remain separate obligations.

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.arc_has_segment_chain_in_open_neighborhood 
    {N M : ℕ} (D : PlaneDrawing N M) (e : Fin M)
    {U : Set (Fin 2 → ℝ)} (hU : IsOpen U)
    (himage : Set.range (D.arc e) ⊆ U) :
    Relation.ReflTransGen (fun a b => segment ℝ a b ⊆ U)
      (D.vertex (D.left e)) (D.vertex (D.right e)) := by sorry
