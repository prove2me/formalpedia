-- Prove2me | solution 1 for Erdos180.thetaCopy_base_center_color_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T02:56:22.500283+00:00
-- url     : https://prove2.me/submissions/a3b5e72b-5b3c-41c5-92d5-2e3d3fd125dc

import Definitions.Def_erdos180_core4
import Mathlib.Combinatorics.SimpleGraph.Coloring.VertexColoring

open Erdos180
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
theorem solution
    {G : SimpleGraph V}
    (color : G.Coloring (Fin 2))
    (copy : SimpleGraph.Copy thetaGraph G)
    (base : Fin 3) (center : Fin 2) :
    color (copy (.inl (.inl base))) =
      color (copy (.inl (.inr center))) := by
  exact bipartite_coloring_eq_of_common_neighbor color
    (copy.toHom.map_rel (theta_base_pair_adj base center))
    (copy.toHom.map_rel (theta_center_pair_adj base center))
