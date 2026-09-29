-- Prove2me | Theorems.Thm_Escher_nonempty_staircase_of_not_isNoetherianRing
-- name    : Escher.nonempty_staircase_of_not_isNoetherianRing
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T08:35:03.457295+00:00
-- url     : https://prove2.me/theorems/90ba78e7-331c-4ff1-a3db-f0153f7df026
-- title:
--   Every non-Noetherian commutative ring carries an Escher staircase.
-- statement:
--   Every non-Noetherian commutative ring carries an Escher staircase.
--
--   ```lean
--   theorem Escher.nonempty_staircase_of_not_isNoetherianRing(h : ¬ IsNoetherianRing R) :
--       Nonempty (Staircase R) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Tropical/EscherStaircase/Core.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Tropical/EscherStaircase/Core.lean#L91

-- Thm stub generated from Tropical/EscherStaircase/Core.lean
import Mathlib
import Definitions.Def_Tropical_EscherStaircase_Core
/-
Copyright (c) 2026. All rights reserved.

# Escher Staircases in Algebra: Infinite Ascending Chains That Loop Back

An *Escher staircase* is an infinite, strictly ascending chain of ideals
`I₀ ⊊ I₁ ⊊ I₂ ⊊ ⋯` in a commutative ring.  The evocative "impossible staircase"
picture asks how such a chain can nevertheless "loop back" to its starting point.
This file makes the phenomenon precise and completely resolves the apparent
paradox.

## Main results

* `Escher.Staircase.iInf_eq_first` — the **loop-back lemma**: the infinite
  intersection `⨅ n, Iₙ` of an *ascending* chain is exactly its first term `I₀`.
  The staircase always "loops back" to where it started; there is nothing
  paradoxical about it.
* `Escher.not_isNoetherianRing_of_staircase` — a ring carrying an Escher staircase
  is not Noetherian.
* `Escher.nonempty_staircase_of_not_isNoetherianRing` — conversely, every
  non-Noetherian ring carries an Escher staircase.
* `Escher.nonempty_staircase_iff_not_isNoetherianRing` — the **characterization**:
  a commutative ring admits an Escher staircase iff it is not Noetherian.  Thus
  the existence of an Escher staircase is a faithful witness of non-Noetherianity.

-- !-- Lab Notes -- !--
## Hypothesis (Hypothesizer)
The description frames an Escher staircase as an ascending chain whose infinite
intersection "loops back" to `I₁`.  Conjecture set:
  (H1) For any ascending chain, `⨅ Iₙ = I₀` automatically (loop-back is free).
  (H2) A ring has such a *strict* ascending chain iff it is non-Noetherian.
  (H3) [surprising] The advertised `Int(ℤ)` example `Iₙ = {f : f(ℤ) ⊆ 2ⁿℤ}` is
       *descending*, not ascending — so the headline example is mislabelled.

## Experiment (Experimenter)
Computed small cases in the Boolean ring `ℕ → 𝔽₂` (see `BooleanRing.lean`).  The
"support < n" ideals give a genuine strict ascending chain with `⨅ = ⊥`, i.e.
`I₀ = ⊥`, confirming (H1).  For `Int(ℤ)`, `2ⁿ⁺¹ℤ ⊆ 2ⁿℤ` forces `I_{n+1} ⊆ Iₙ`,
confirming (H3): the classic example is a *descending* Anti-Escher chain, matching
`Logic/ChainInvariants.lean`.

## Analysis (Analyst)
(H1) is a one-line lattice fact once phrased correctly.  (H2) is the substantive
theorem: it identifies "carries an Escher staircase" with `¬ IsNoetherianRing`,
turning an evocative picture into a lattice-theoretic invariant.  The forward
direction extracts a strict chain from the failure of the ascending chain
condition via `RelEmbedding.wellFounded_iff_isEmpty`.

## Critique (Critic)
The loop-back lemma alone is near-trivial, so it is *not* a main theorem; the
main result is the biconditional characterization.  We guard against vacuity by
also exhibiting a concrete non-Noetherian model (`BooleanRing.lean`) and by
contrasting with the ℤ Anti-Escher theorem imported from the catalog.

## Synthesis
"Escher staircase" = strict ascending ideal chain = certificate of
non-Noetherianity; the loop-back is automatic and the paradox dissolves.
-- !-- Lab Notes -- !--
-/

open Escher

variable {R : Type*} [CommRing R]


open Staircase

theorem Escher.nonempty_staircase_of_not_isNoetherianRing(h : ¬ IsNoetherianRing R) :
    Nonempty (Staircase R) := by sorry
