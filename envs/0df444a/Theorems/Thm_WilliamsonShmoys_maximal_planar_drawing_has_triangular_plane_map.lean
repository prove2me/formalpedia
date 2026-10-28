-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_has_triangular_plane_map
-- name    : WilliamsonShmoys.maximal_planar_drawing_has_triangular_plane_map
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T17:30:50.99997+00:00
-- url     : https://prove2.me/theorems/a8a0f1d5-6f00-4634-a5ce-7524a9f9c8af
-- title:
--   Maximal planar drawings yield triangular face data
-- statement:
--   Construct a finite type of faces, each with a three-edge boundary in the graph, such that every graph edge lies on exactly two faces and the vertex-face-edge counts satisfy Euler’s relation. The hypothesis of at least three vertices includes the triangle boundary case; the two sides of a triangular embedding are distinct faces even though their boundaries coincide.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.maximal_planar_drawing_has_triangular_plane_map
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hMax : forall M : SimpleGraph V,
      Set.Subset L.edgeSet M.edgeSet ->
      WilliamsonShmoys.HasPlanarDrawingOn M ->
      Set.Subset M.edgeSet L.edgeSet)
    (hCard : 3 <= Fintype.card V) :
    ∃ (F : Type) (faceInst : Fintype F)
      (boundary : F → Finset (Sym2 V)),
      (∀ f, (boundary f).card = 3) ∧
      (∀ f, ∀ e ∈ boundary f, e ∈ L.edgeSet) ∧
      (∀ e ∈ L.edgeSet,
        ((@Finset.univ F faceInst).filter (fun f => e ∈ boundary f)).card = 2) ∧
      Fintype.card V + @Fintype.card F faceInst = L.edgeSet.ncard + 2 := by sorry
