-- Prove2me | Theorems.Thm_NoBorelUpperBoundFSigma_corollary4_linear_cosets
-- name    : NoBorelUpperBoundFSigma.corollary4_linear_cosets
-- status  : Open
-- author  : @username
-- created : 2026-11-02T02:43:23.484945+00:00
-- url     : https://prove2.me/theorems/26557902-98c3-433a-8694-e292a5380161
-- title:
--   Corollary 4 — no Borel bound for linear cosets on fixed real $\ell_1$
-- statement:
--   For every Polish target Y and every Borel equivalence relation F on Y, there is a real linear subspace $H\subseteq\ell_1(\mathbb N;\mathbb R)$ such that H is F-sigma, the coset graph $\{(x,y):y-x\in H\}$ is F-sigma, and $E_H$ has no Borel measurable reduction to F. The source has its native real norm topology. H is algebraic and need not be closed.
--
--   **Formalization note.** The manuscript uses one fixed separable Banach space isomorphic to real ell_1; the statement transports it to standard real lp with exponent 1. The graph conclusion follows from continuity of subtraction. Empty targets are included.
-- source:
--   No Borel upper bound for the F_sigma equivalence relations, research proof note dated 1 November 2026, supplied manuscript UniversalBorelEquivalence-20261101.tex, Section 4, Corollary 4, lines 349–353 and its fixed-space identification in the proof.

import Definitions.Def_NoBorelUpperBound20261101

set_option autoImplicit false
universe u

theorem NoBorelUpperBoundFSigma.corollary4_linear_cosets
    {Y : Type u} [TopologicalSpace Y] [PolishSpace Y]
    (F : Setoid Y) (hF : NoBorelUpperBoundFSigma.IsBorelRelation F.r) :
    ∃ H : Submodule ℝ NoBorelUpperBoundFSigma.RealL1,
      NoUniversalFSigma.IsFSigma (H : Set NoBorelUpperBoundFSigma.RealL1) ∧
      NoUniversalFSigma.IsFSigmaRelation (NoBorelUpperBoundFSigma.LinearCosetRelation H) ∧
      ¬ NoBorelUpperBoundFSigma.BorelReducible (NoBorelUpperBoundFSigma.LinearCosetRelation H) F.r := by sorry
