-- Prove2me | Definitions.Def_ErdosProblems_Erdos1049_ZudilinConeArithmetic
-- name    : ErdosProblems_Erdos1049_ZudilinConeArithmetic
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-27T17:45:17.317221+00:00
-- url     : https://prove2.me/theorems/a9c28f44-610d-4f69-9352-ac60ee83583c
-- title:
--   Erdős #1049: endpoint arithmetic for the Heine--Zudilin cone
-- statement:
--   Endpoint jet and scalar-cone arithmetic uses exact modular signatures, polynomial evaluations, and pigeonhole constraints independently of analytic source estimates. The submitted module contains the source declarations zudilinNormExpTwice, zudilinPartialFractionExpTwice, zudilinBottomExpTwice, zudilinRawDegreeTwice, zudilinBottomExpTwice_at_a2, among others. Source topic: Erdős #1049: endpoint arithmetic for the Heine--Zudilin cone.
-- source:
--   Pinned Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos1049/ZudilinConeArithmetic.lean#L26-L448
--   Paper exposition and prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/1049/erdos-1049-rational-base-lambert.tex#L1252-L1257
--   Correspondence: Erdős #1049 formal source; Zudilin is credited for the relevant rational-base Lambert-series method, without a novelty or all-rational-base claim.

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Coprime
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.Tactic

/-!
# Erdős #1049: endpoint arithmetic for the Heine--Zudilin cone

This module isolates the source-independent arithmetic behind the returned
scalar-cone obstruction at the rational base `3 / 2`.  It does not construct
the Zudilin coefficient polynomials or import their analytic asymptotics.

The key finite observation is that homogeneous evaluation at `(3,2)` sees the
bottom polynomial endpoint modulo `3` and the top endpoint modulo `2`.
Consequently a unit at either endpoint prevents a common local factor.  The
endpoint-jet definitions record the exact additive congruence problem left
after scalar and multiplicative deformations have been exhausted.
-/

namespace ErdosProblems.Erdos1049

open Polynomial













































/-! ## Generic homogeneous evaluation and the cyclotomic endpoint theorem -/

/-- Integer homogeneous evaluation at a reduced numerator--denominator pair.

The existing `homEvalThreeTwo` is the specialization `(a,b) = (3,2)`.  This
generic form is the arithmetic object used in Proposition 3.6 of the paper. -/
def homEval (a b W : ℕ) (P : Polynomial ℤ) : ℤ :=
  ∑ i ∈ Finset.range (W + 1), P.coeff i * a ^ i * b ^ (W - i)



























end ErdosProblems.Erdos1049


