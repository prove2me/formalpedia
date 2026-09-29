-- Prove2me | Theorems.Thm_Catalog_NET73_AttentionProfile_kneeAt_ge_of_concentration
-- name    : Catalog.NET73.AttentionProfile.kneeAt_ge_of_concentration
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:27:24.68786+00:00
-- url     : https://prove2.me/theorems/4ec32984-f644-4353-bb07-9381d1222b7b
-- title:
--   Concentration law.
-- statement:
--   **Concentration law.** If the heaviest key of a domain carries at most `m`
--   of the attention mass (and hence every key does), the knee is at least `τ / m`.
--   The knee is therefore driven by the *shape* of the attention distribution.
--
--   ```lean
--   theorem Catalog.NET73.AttentionProfile.kneeAt_ge_of_concentration{τ m : ℚ} (hm : 0 < m) (hτ : τ < 1)
--       (hstep : ∀ j, P.cum (j + 1) - P.cum j ≤ m) :
--       τ / m ≤ (P.kneeAt τ : ℚ) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/NET73KneeDecoupling.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/NET73KneeDecoupling.lean#L119

-- Thm stub generated from Applications/NET73KneeDecoupling.lean
import Mathlib
import Definitions.Def_Applications_NET73KneeDecoupling
import Definitions.Def_Applications_NET73TokenizationDensity
/-
# NET-73, structural side: the knee is a concentration functional,
# provably decoupled from tokenization density

`Applications/NET73TokenizationDensity.lean` refutes the tokenization
hypothesis on the measured data.  This file explains *why* such a refutation was
possible at all, by isolating the quantity that does control the knee.

A **domain** is modelled by an attention profile: a tokens-per-word number
`tpw` (a surface statistic of the tokenizer) together with the *capture curve*
`cum k` = fraction of attention mass carried by the `k` heaviest keys.  The
knee at tolerance `τ` is the least `k` whose top-`k` keys already capture `τ`
of the mass.

Main results.

* `kneeAt_spec` / `lt_of_lt_kneeAt` — the knee is well defined and is the least
  such `k`; `kneeAt_mono_tol`, `kneeAt_mono_profile`, `kneeAt_congr` — it is
  monotone in the tolerance, *antitone* in the capture curve (a strictly more
  concentrated domain never needs more keys), and depends on nothing but the
  capture curve.
* `cum_le_of_step_le` and `kneeAt_ge_of_concentration` — the **concentration
  law**: if no single key carries more than `m` of the mass, then
  `k* ≥ τ / m`.  Proved by induction along the capture curve.
* `kneeAt_uniform` — the bound is tight: the uniform-mass profile with per-key
  mass `τ / k` has knee exactly `k`.
* `tpw_knee_decoupled` — **decoupling**: every pair (tokens-per-word `d`,
  knee `k`) is realised by some domain.  Hence `no_tpw_functional_law`: there is
  no function whatsoever — monotone or not — from tokens-per-word to the knee.
* `net73_data_realisable_by_concentration` — the four measured NET-73 points are
  jointly realised by concentration alone, at a single fixed tolerance.

So the knee is a *relational* functional of the attention mass profile; the
NET-73 numbers are exactly what the decoupling theorem predicts.
-/

open Catalog.NET73

/-! ## 1. Attention profiles and the knee -/


open AttentionProfile

variable (P Q : AttentionProfile)










/-! ## 2. The concentration law -/

theorem Catalog.NET73.AttentionProfile.kneeAt_ge_of_concentration{τ m : ℚ} (hm : 0 < m) (hτ : τ < 1)
    (hstep : ∀ j, P.cum (j + 1) - P.cum j ≤ m) :
    τ / m ≤ (P.kneeAt τ : ℚ) := by sorry
