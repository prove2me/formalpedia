-- Prove2me | Theorems.Thm_Catalog_NET73_quadUniform_knee_three
-- name    : Catalog.NET73.quadUniform_knee_three
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:28:20.846293+00:00
-- url     : https://prove2.me/theorems/ca6abe35-0aaa-44b5-96cc-ff6f9609234c
-- title:
--   The participation bound is attained on this domain: at tolerance `3/4` it
-- statement:
--   The participation bound is attained on this domain: at tolerance `3/4` it
--   predicts `k* ≥ 9/4`, and the true knee is `3`.
--
--   ```lean
--   theorem Catalog.NET73.quadUniform_knee_three(d : ℚ) :
--       (quadUniform.toProfile d).kneeAt (3/4) = 3 ∧
--       (3 / 4 : ℚ) ^ 2 / quadUniform.collision ≤ 3 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/NET73ConcentrationSpectrum.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/NET73ConcentrationSpectrum.lean#L172

-- Thm stub generated from Applications/NET73ConcentrationSpectrum.lean
import Mathlib
import Definitions.Def_Applications_NET73ConcentrationSpectrum
import Definitions.Def_Applications_NET73KneeDecoupling
/-
# NET-73, cycle 2: the concentration spectrum of a domain

`Applications/NET73KneeDecoupling.lean` shows that the knee `k*` is a functional
of the attention capture curve and is decoupled from tokens-per-word.  This file
asks the follow-up question the NET-73 verdict poses — *what relational
statistic does control the knee?* — and answers it with two independent bounds
and one exactly solvable family.

* **Participation bound** (`kneeAt_ge_sq_div_collision`).  For a domain whose
  attention mass vector is `p` with collision index `S = ∑ p i ^ 2` (the
  Rényi-2 / inverse-participation statistic), the knee obeys
  `k* ≥ τ² / S`.  The proof is Cauchy–Schwarz on the top-`k` block, so the
  bound is information-theoretic: the effective number of participating keys
  `1/S` lower-bounds (up to `τ²`) how many keys must be kept.
* **Top-mass bound** (`kneeAt_ge_tol_div_top`).  For a sorted mass vector the
  knee is at least `τ / p 0`: a domain with a single dominant key has a small
  knee, no matter how many tokens its words cost.
* **Geometric family** (`kneeAt_geometric_le_iff`).  For the exactly solvable
  decay profile `cum k = 1 - r ^ k` the knee is characterised by
  `k* ≤ k ↔ r ^ k ≤ 1 - τ`, is monotone in the decay rate `r`, and produces
  `geometric_domain_shift_at_equal_density`: two domains with *identical*
  tokens-per-word whose knees are `2` and `14` at the same tolerance — the
  in-model analogue of code (`k* = 12`) versus French (`k* > 32`).

Together these say the domain shift lives on the decay-rate axis, exactly where
NET-73's refutation of tokenization density pushes it.
-/

open Catalog.NET73

open Finset AttentionProfile

/-! ## 1. Domains presented by a sorted attention mass vector -/


open MassVector

variable (M : MassVector)














/-! ## 2. A worked domain: four equally weighted keys -/

theorem Catalog.NET73.quadUniform_knee_three(d : ℚ) :
    (quadUniform.toProfile d).kneeAt (3/4) = 3 ∧
    (3 / 4 : ℚ) ^ 2 / quadUniform.collision ≤ 3 := by sorry
