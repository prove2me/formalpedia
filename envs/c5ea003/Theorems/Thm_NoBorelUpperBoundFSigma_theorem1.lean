-- Prove2me | Theorems.Thm_NoBorelUpperBoundFSigma_theorem1
-- name    : NoBorelUpperBoundFSigma.theorem1
-- status  : Proved
-- author  : @username
-- created : 2026-11-02T02:43:41.071946+00:00
-- url     : https://prove2.me/theorems/56adfcf7-9df7-4730-b48d-1968cd83b344
-- title:
--   Theorem 1 — no Borel upper bound for all $F_\sigma$ equivalence relations
-- statement:
--   For every Polish space Y, there is no equivalence relation F on Y such that its graph is Borel and every equivalence relation E with an F-sigma graph on every Polish space X Borel reduces to F. Explicitly, there is no such F for which every pair $(X,E)$ admits a Borel map $f:X\to Y$ satisfying $E(x,x^{\prime})\iff F(f(x),f(x^{\prime}))$ for all source pairs. The target graph may have arbitrary Borel complexity; no F-sigma hypothesis is imposed on it. The source spaces are not required to be compact or sigma-compact.
--
--   **Formalization note.** Polish sources range over the ordinary Lean type universe, containing the standard presentations of all Polish spaces; the target universe is arbitrary. Empty spaces are permitted. Borel measurability and graph Borelness use the specified topologies.
-- source:
--   No Borel upper bound for the F_sigma equivalence relations, research proof note dated 1 November 2026, supplied manuscript UniversalBorelEquivalence-20261101.tex, Section 1, Theorem 1, lines 48–51; conventions in lines 35–46.

import Definitions.Def_NoBorelUpperBound20261101

set_option autoImplicit false
universe u

theorem NoBorelUpperBoundFSigma.theorem1
    {Y : Type u} [TopologicalSpace Y] [PolishSpace Y] :
    ¬ ∃ F : Setoid Y,
      NoBorelUpperBoundFSigma.IsBorelRelation F.r ∧
      NoBorelUpperBoundFSigma.IsFSigmaUpperBound F.r := by sorry
