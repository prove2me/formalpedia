-- Prove2me | Definitions.Def_Novelty_AnalyticCensus
-- name    : Novelty_AnalyticCensus
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:01:47.424527+00:00
-- url     : https://prove2.me/theorems/0ec16621-1d75-409d-b96c-b766bcc46224
-- title:
--   Aether Catalog definitions — Novelty_AnalyticCensus
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.AnalyticCensus`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/AnalyticCensus.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The L-Function Universe, part IV: the *analytic* census is faithful

Earlier parts of this project (`NaiveUniverse`, `PeriodicUniverse`, `SelbergCensus`)
studied the L-function universe *combinatorially*: an L-function was modelled by a
finite/periodic packet of coefficient data, and the theme was that the space of such
data packets is countable.

This file goes **deeper**, to the genuine *analytic* object.  An L-function here is a
concrete Dirichlet series

  `LSeries f (s) = ∑' n, f n / n ^ s`

viewed as an actual function `ℂ → ℂ`, built from a coefficient sequence `f : ℕ → ℂ`.
The census philosophy — "each L-function is pinned down by its coefficient data" — is
no longer a modelling convention: it is a **theorem** about the analytic function,
namely the rigidity/uniqueness result that a Dirichlet series which converges
somewhere is uniquely determined by its coefficients
(Mathlib's `LSeries_injOn`).  We build a chain of consequences on top of this hub:

* `abscissa_lt_top_of_summable`, `abscissa_lt_top_of_bounded` — convergence input;
* `lseries_inj` — **rigidity**: normalized, convergent coefficient sequences inject
  into their analytic L-functions;
* `zeta_rigidity` — the Riemann zeta function is the *unique* Dirichlet series (with
  `f 0 = 0`, convergent) taking its values;
* `spikeLSeries_injective` / `analytic_universe_infinite` — the monomial Dirichlet
  series `n ↦ (k+1)^{-s}` are pairwise distinct as analytic functions, so the
  analytic L-function universe is **infinite**;
* `charLSeries_injOn_fixedMod` / `charCensusEquiv` — for each modulus the Dirichlet
  characters correspond **bijectively** to their analytic L-functions (the census is
  *exact*, no accidental coincidences);
* `analyticDirichletUniverse_countable` — the whole family of Dirichlet L-functions,
  as analytic functions over all moduli, is **countable**.

Together these upgrade the combinatorial census to an honest statement about the
analytic objects: the universe of Dirichlet L-functions is countably infinite and
faithfully indexed by its arithmetic data.

The file is self-contained and imports only Mathlib.
-/

open LSeries Complex

namespace AnalyticLFunctionCensus

/-! ## Convergence inputs

An L-function only "exists" (is determined by its coefficients) once it converges
somewhere.  These two lemmas record the two ways we obtain convergence in this file:
from a single summable point, and from a bound on the coefficients. -/



/-! ## The rigidity hub

The central fact powering the whole census: a Dirichlet series which converges
somewhere is completely determined by its coefficient sequence.  Equivalently, the
map `f ↦ LSeries f` is injective on normalized (`f 0 = 0`), convergent sequences. -/


/-! ## The Riemann zeta function is rigid

`ζ(s) = ∑ n⁻ˢ` is the L-function of the (normalized) constant coefficient sequence.
Rigidity says it is the *only* convergent Dirichlet series taking its values. -/

/-- The (normalized) coefficient sequence of the Riemann zeta function: `1` at every
positive integer, `0` at `0`. -/
def zetaCoeff : ℕ → ℂ := fun n => if n = 0 then 0 else 1




/-! ## The monomial family: the analytic universe is infinite

The simplest infinite family of honest Dirichlet series: the "monomials"
`spike k`, whose L-function is `s ↦ (k+1)⁻ˢ`.  Distinct `k` give distinct
coefficient sequences, hence — by rigidity — distinct analytic L-functions. -/

/-- The monomial coefficient sequence: `1` at position `k+1`, `0` elsewhere.  Its
L-function is `s ↦ (k+1)⁻ˢ`. -/
def spike (k : ℕ) : ℕ → ℂ := fun n => if n = k + 1 then 1 else 0







/-! ## The Dirichlet family: exactness and countability

The genuine arithmetic L-functions of degree one are the Dirichlet L-functions
`L(s, χ) = ∑ χ(n) n⁻ˢ`.  Their coefficient sequences are bounded (`|χ(n)| ≤ 1`), so
they converge and rigidity applies.  We obtain:

* per modulus, the characters correspond **bijectively** to their L-functions;
* over all moduli, the analytic Dirichlet family is **countable**. -/

/-- The (normalized) coefficient sequence `n ↦ χ(n)` of a Dirichlet character `χ`
modulo `N`, with the `n = 0` term set to `0`. -/
noncomputable def charCoeff {N : ℕ} (χ : DirichletCharacter ℂ N) : ℕ → ℂ :=
  fun n => if n = 0 then 0 else χ (n : ZMod N)








/-- The analytic Dirichlet L-function attached to a character bundled with its
modulus. -/
noncomputable def analyticDirichletFamily (p : Σ N : ℕ, DirichletCharacter ℂ N) : ℂ → ℂ :=
  LSeries (charCoeff p.2)


end AnalyticLFunctionCensus


