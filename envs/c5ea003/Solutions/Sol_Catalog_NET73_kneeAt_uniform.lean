-- Prove2me | solution 1 for Catalog.NET73.kneeAt_uniform
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:07:45.250325+00:00
-- url     : https://prove2.me/submissions/18f36757-8d2b-4be2-a13d-48786ee62095

-- Sol generated from Applications/NET73KneeDecoupling.lean
import Mathlib
import Definitions.Def_Applications_NET73KneeDecoupling
import Definitions.Def_Applications_NET73TokenizationDensity
import Theorems.Thm_Catalog_NET73_AttentionProfile_kneeAt_le
import Theorems.Thm_Catalog_NET73_AttentionProfile_kneeAt_spec
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




/-! ## 3. Realising every (density, knee) pair -/

open AttentionProfile









open Catalog.NET73 in
theorem solution{d τ : ℚ} {k : ℕ} (hτ0 : 0 < τ) (hτ1 : τ < 1) (hk : 0 < k) :
    (uniformProfile d τ k hτ0 hk).kneeAt τ = k := by
  set P := uniformProfile d τ k hτ0 hk with hP
  have hk' : (0 : ℚ) < (k : ℚ) := by exact_mod_cast hk
  have hcum : ∀ j : ℕ, P.cum j = min 1 ((j : ℚ) * τ / k) := fun j => rfl
  have hle : P.kneeAt τ ≤ k := by
    refine P.kneeAt_le ?_
    rw [hcum k]
    have : (k : ℚ) * τ / k = τ := by field_simp
    rw [this]
    exact le_min hτ1.le le_rfl
  refine le_antisymm hle ?_
  by_contra hlt
  push_neg at hlt
  have hj : P.cum (P.kneeAt τ) < τ := by
    rw [hcum]
    have hlt' : ((P.kneeAt τ : ℕ) : ℚ) < (k : ℚ) := by exact_mod_cast hlt
    have : ((P.kneeAt τ : ℕ) : ℚ) * τ / k < τ := by
      rw [div_lt_iff₀ hk']
      nlinarith
    exact lt_of_le_of_lt (min_le_right _ _) this
  exact absurd (P.kneeAt_spec hτ1) (not_le.mpr hj)
