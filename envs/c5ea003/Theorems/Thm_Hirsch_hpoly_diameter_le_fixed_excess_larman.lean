-- Prove2me | Theorems.Thm_Hirsch_hpoly_diameter_le_fixed_excess_larman
-- name    : Hirsch.hpoly_diameter_le_fixed_excess_larman
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-12T17:27:57.457965+00:00
-- url     : https://prove2.me/theorems/49576ed3-5185-4951-9215-43283ef6169e
-- title:
--   A dimension-independent Larman bound at fixed row excess
-- statement:
--   Let $E,d,n$ be nonnegative integers and let $P$ be a bounded
--   polyhedron in $\mathbb R^d$ described by $n$ linear inequalities. If $n\le d+E$,
--   then every pair of vertices can be joined by an ordinary edge walk of length at most
--
--   $$2E\,2^{\max(E-3,0)}.$$
--
--   Empty and lower-dimensional polyhedra, redundant inequalities, and zero row
--   normals are included. Thus a fixed bound on row excess gives a diameter bound
--   independent of ambient dimension. This classical coarse bound remains exponential
--   in excess and does not establish the Polynomial Hirsch conjecture.
--
--   **Formalization Note** The exponent uses truncated natural subtraction. The
--   predicate permits stationary steps, expressing an upper bound on edge distance.
-- source:
--   Exact H-polyhedron statement and proof: https://github.com/jjoshua2/prove2me-work/blob/117709458ec4b071dc846cd8443feea19ca2669b/Solutions/PolynomialFixedExcessLarman.lean#L21 ; classical shared-facet descent: Santos, A counterexample to the Hirsch conjecture (2012), Lemma 1.1 and its proof, printed pp. 385 and 391; https://annals.math.princeton.edu/wp-content/uploads/annals-v176-n1-p07-p.pdf . The explicit coarse constant here is derived from the platform Larman bound, not claimed to be a verbatim theorem of Santos.

import Mathlib
import Definitions.Def_Hirsch_model
open scoped RealInnerProductSpace
open Set Hirsch

namespace Hirsch
theorem hpoly_diameter_le_fixed_excess_larman
    (E d n : ℕ)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hrows : n ≤ d + E) (hbd : Bornology.IsBounded (Hpoly a b)) :
    DiamLE (Hpoly a b) (2 * E * 2 ^ (E - 3)) := by sorry
end Hirsch
