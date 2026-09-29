-- Prove2me | Theorems.Thm_BookSixth_planar_euler_counting_shell
-- name    : BookSixth.planar_euler_counting_shell
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-17T23:41:51.412792+00:00
-- url     : https://prove2.me/theorems/ff167e3c-b48c-4154-8c5d-a231cc6026d2
-- title:
--   Euler counting shell for the planar edge bound
-- statement:
--   If a connected planar drawing has nV >= 3 vertices, nE edges and nF faces satisfying Euler's formula nV - nE + nF = 2 and the face-edge incidence bound 3*nF <= 2*nE (every face incident to at least three edge-sides, every edge incident to at most two faces), then nE <= 3*nV - 6. This is the pure counting shell of the planar edge estimate used in Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), Chapter 45, Theorem 4, p. 317. It isolates the arithmetic consequence of the Euler and incidence inputs; the geometric construction of the face count from continuous drawing arcs remains with the parent BookSixth.crossing_free_subset_edge_bound.
-- source:
--   Counting shell of the planar simple-graph edge estimate in Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), Chapter 45, Theorem 4, p. 317, https://doi.org/10.1007/978-3-662-57265-8_45. Reduction component for parent BookSixth.crossing_free_subset_edge_bound (b2255bec-31ff-4bf9-84b4-81705574eaac): it discharges the arithmetic step once Euler and face-incidence inputs are available, leaving the geometric face construction as the remaining parent obligation.

import Mathlib
open scoped BigOperators

theorem BookSixth.planar_euler_counting_shell (nV nE nF : ℕ) (hV : 3 ≤ nV) (hEuler : nV + nF = nE + 2) (hinc : 3 * nF ≤ 2 * nE) : nE ≤ 3 * nV - 6 := by sorry
