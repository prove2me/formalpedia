-- Prove2me | Theorems.Thm_IharaZeta_root_norm_of_ramanujan
-- name    : IharaZeta.root_norm_of_ramanujan
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:03:42.819673+00:00
-- url     : https://prove2.me/theorems/380b53ba-d18d-42c5-9692-151a7e61ebbf
-- title:
--   Root norm of ramanujan
-- statement:
--   Formal statement of `IharaZeta.root_norm_of_ramanujan` from the Aether Catalog (Novelty). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem IharaZeta.root_norm_of_ramanujan(q lam : ℝ) (hq : 0 < q)
--       (hlam : |lam| ≤ 2 * Real.sqrt q) (u : ℂ) (hu : iharaFactor q lam u = 0) :
--       ‖u‖ = 1 / Real.sqrt q := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/IharaZetaRamanujanRH.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/IharaZetaRamanujanRH.lean#L102

-- Thm stub generated from Novelty/IharaZetaRamanujanRH.lean
import Mathlib
import Definitions.Def_Novelty_IharaZetaRamanujanRH
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Riemann Hypothesis for the Ihara zeta function of a regular graph

The Ihara zeta function of a finite connected `(q+1)`-regular graph `G` on `n`
vertices admits the closed determinantal form

    ζ_G(u)⁻¹ = (1 - u²)^{(n-1)(q-1)/2} · det(I - A u + q u² I),

where `A` is the adjacency matrix.  Its non-trivial poles are therefore the
reciprocals of the roots of the *local factors*

    p_λ(u) = q u² - λ u + 1,   λ ∈ spec(A),

one factor per adjacency eigenvalue `λ`.  The **Riemann Hypothesis for `ζ_G`**
asks that every non-trivial pole lie on the circle `|u| = 1/√q`; equivalently
that every root of each non-trivial local factor lie on that circle.

This file isolates and proves the arithmetic heart of Ihara's theorem: a single
local factor `p_λ` has *all* of its complex roots on the circle `|u| = 1/√q`
**iff** the eigenvalue satisfies the Ramanujan bound `|λ| ≤ 2√q`.  Summed over
the spectrum this is exactly the statement

    ζ_G satisfies the Riemann Hypothesis  ⇔  G is a Ramanujan graph.

The argument is a genuine bridge between complex analysis (location of the roots
of a quadratic), real algebra (the discriminant / Vieta relations) and spectral
graph theory (the Ramanujan spectral gap).

## Main results

* `iharaFactor` — the local factor `q u² - λ u + 1` attached to an eigenvalue.
* `root_norm_of_ramanujan` — Ramanujan bound ⇒ every root sits on `|u| = 1/√q`.
* `ramanujan_of_root_norm` — the converse: if every root sits on the circle then
  the Ramanujan bound holds.
* `ihara_RH_iff_ramanujan` — the equivalence "RH for the local factor ⇔ Ramanujan".
* `trivial_eigenvalue_factor`, `trivial_eigenvalue_breaks_RH` — the boundary
  phenomenon: the *trivial* eigenvalue `λ = q + 1` factors the local polynomial
  as `(q u - 1)(u - 1)`, whose roots `1` and `1/q` do **not** lie on the circle,
  which is precisely why the Riemann Hypothesis is imposed only on the
  non-trivial spectrum.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer).  The Ihara/Ramanujan correspondence "RH ⇔ Ramanujan"
should reduce, factor by factor, to a purely quadratic statement: the two roots
of `q u² - λ u + 1` lie on the circle of radius `1/√q` exactly when `λ² ≤ 4q`.
The bold claim is that this scalar lemma already contains the full spectral
content of Ihara's theorem.

Experiment (Experimenter).  Formalised the local factor and proved both
directions.  Forward direction: for a root `u`, conjugating the defining
equation and combining with the original gives either `u` real (forcing the
discriminant to be non-negative, hence `λ² = 4q` at the Ramanujan boundary and
`u² = 1/q`), or `u + ū = λ/q`, whence adding the equation to its conjugate
yields `u ū = 1/q`, i.e. `normSq u = 1/q`.  Converse: when `λ² > 4q` the two
*distinct real* roots `r± = (λ ± √(λ²-4q))/(2q)` have product `1/q > 0`, so they
share a sign; if both had modulus `1/√q` they would be equal, contradicting
distinctness.

Analysis (Analyst).  The whole spectral theorem collapses onto a discriminant
sign test.  The "trivial" eigenvalue `λ = q+1` is exactly the case where the
discriminant is a perfect square `(q-1)²` and the roots escape the circle to the
real points `1` and `1/q`; this is the structural reason RH is stated only for
the non-trivial spectrum.

Critique (Critic).  Guarded against vacuity: `iharaFactor` is a genuine degree-2
polynomial with `q ≠ 0`, so it always has complex roots and the universally
quantified statements are non-empty.  The boundary lemma exhibits an explicit
counterexample to the naive (unrestricted) RH, ruling out a vacuously true
reading.

Synthesis (PI).  The equivalence `ihara_RH_iff_ramanujan` packages the two
directions; the trivial-eigenvalue lemmas delimit its scope.
-- !-- Lab Notes -- !--
-/


open Complex

open IharaZeta



/-
**Ramanujan ⇒ Riemann Hypothesis (local factor).**  If the eigenvalue `λ`
satisfies the Ramanujan bound `|λ| ≤ 2√q`, then every complex root of the local
factor lies on the circle `|u| = 1/√q`.
-/

theorem IharaZeta.root_norm_of_ramanujan(q lam : ℝ) (hq : 0 < q)
    (hlam : |lam| ≤ 2 * Real.sqrt q) (u : ℂ) (hu : iharaFactor q lam u = 0) :
    ‖u‖ = 1 / Real.sqrt q := by sorry
