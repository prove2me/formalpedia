-- Prove2me | Theorems.Thm_Catalog_NET73_geometric_domain_shift_at_equal_density
-- name    : Catalog.NET73.geometric_domain_shift_at_equal_density
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:28:07.883107+00:00
-- url     : https://prove2.me/theorems/b39f062b-0b04-4881-9fc2-1d8e704b9a1c
-- title:
--   The domain shift, reproduced inside the model.
-- statement:
--   **The domain shift, reproduced inside the model.**  Two domains with the
--   *same* tokens-per-word `d` but decay rates `1/2` and `9/10` have knees `2` and
--   `14` at the same tolerance `3/4`: a sevenfold gap generated purely by attention
--   decay, mirroring code (`k* = 12`) versus French (`k* > 32`) at nearly equal
--   token density.
--
--   ```lean
--   theorem Catalog.NET73.geometric_domain_shift_at_equal_density(d : ℚ) :
--       (geometricProfile d (1/2) (by norm_num) (by norm_num)).kneeAt (3/4) = 2 ∧
--       (geometricProfile d (9/10) (by norm_num) (by norm_num)).kneeAt (3/4) = 14 ∧
--       (geometricProfile d (1/2) (by norm_num) (by norm_num)).tpw =
--         (geometricProfile d (9/10) (by norm_num) (by norm_num)).tpw := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/NET73ConcentrationSpectrum.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/NET73ConcentrationSpectrum.lean#L243

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






/-! ## 3. The exactly solvable decay family -/

theorem Catalog.NET73.geometric_domain_shift_at_equal_density(d : ℚ) :
    (geometricProfile d (1/2) (by norm_num) (by norm_num)).kneeAt (3/4) = 2 ∧
    (geometricProfile d (9/10) (by norm_num) (by norm_num)).kneeAt (3/4) = 14 ∧
    (geometricProfile d (1/2) (by norm_num) (by norm_num)).tpw =
      (geometricProfile d (9/10) (by norm_num) (by norm_num)).tpw := by sorry
