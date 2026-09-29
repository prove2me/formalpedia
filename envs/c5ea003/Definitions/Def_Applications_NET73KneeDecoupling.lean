-- Prove2me | Definitions.Def_Applications_NET73KneeDecoupling
-- name    : Applications_NET73KneeDecoupling
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:52:25.278983+00:00
-- url     : https://prove2.me/theorems/83c46042-7308-46ea-aa89-3f16e6ff1249
-- title:
--   Aether Catalog definitions — Applications_NET73KneeDecoupling
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.NET73KneeDecoupling`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/NET73KneeDecoupling.lean by skeleton subtraction
import Mathlib
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

namespace Catalog.NET73

/-! ## 1. Attention profiles and the knee -/

/-- A domain, as seen by the limited-memory axis: a tokenizer density together
with the cumulative attention mass captured by the `k` heaviest keys. -/
structure AttentionProfile where
  /-- Tokens per word of the tokenizer on this domain. -/
  tpw : ℚ
  /-- `cum k` = attention mass carried by the `k` heaviest keys. -/
  cum : ℕ → ℚ
  /-- No keys capture no mass. -/
  cum_zero : cum 0 = 0
  /-- Adding keys never loses mass. -/
  cum_mono : Monotone cum
  /-- The captured mass is a fraction. -/
  cum_le_one : ∀ k, cum k ≤ 1
  /-- Every tolerance short of the full mass is eventually met. -/
  approaches_one : ∀ τ : ℚ, τ < 1 → ∃ k, τ ≤ cum k

namespace AttentionProfile

variable (P Q : AttentionProfile)

/-- The knee: the least number of retained keys capturing a fraction `τ`. -/
noncomputable def kneeAt (τ : ℚ) : ℕ := sInf {k | τ ≤ P.cum k}









/-! ## 2. The concentration law -/



end AttentionProfile

/-! ## 3. Realising every (density, knee) pair -/

open AttentionProfile

/-- The uniform-mass domain: each of the first `k` keys carries `τ / k` of the
mass, so the tolerance `τ` is met exactly at the `k`-th key.  Its tokenizer
density `d` is a free parameter, unconstrained by its attention shape. -/
noncomputable def uniformProfile (d τ : ℚ) (k : ℕ) (hτ : 0 < τ) (hk : 0 < k) :
    AttentionProfile where
  tpw := d
  cum := fun j => min 1 (j * τ / k)
  cum_zero := by simp
  cum_le_one := fun j => min_le_left _ _
  cum_mono := by
    intro a b hab
    have hk' : (0 : ℚ) < (k : ℚ) := by exact_mod_cast hk
    have hab' : (a : ℚ) ≤ (b : ℚ) := by exact_mod_cast hab
    have : (a : ℚ) * τ / k ≤ (b : ℚ) * τ / k := by
      gcongr
    exact min_le_min le_rfl this
  approaches_one := by
    intro σ _
    refine ⟨k * ⌈τ⁻¹⌉₊, ?_⟩
    have hk' : (0 : ℚ) < (k : ℚ) := by exact_mod_cast hk
    have hceil : τ⁻¹ ≤ (⌈τ⁻¹⌉₊ : ℚ) := Nat.le_ceil _
    have h1 : (1 : ℚ) ≤ ((k * ⌈τ⁻¹⌉₊ : ℕ) : ℚ) * τ / k := by
      push_cast
      rw [le_div_iff₀ hk']
      have : (1 : ℚ) ≤ (⌈τ⁻¹⌉₊ : ℚ) * τ := by
        have := mul_le_mul_of_nonneg_right hceil (le_of_lt hτ)
        rwa [inv_mul_cancel₀ (ne_of_gt hτ)] at this
      nlinarith
    have hfull : (1 : ℚ) ≤ min 1 (((k * ⌈τ⁻¹⌉₊ : ℕ) : ℚ) * τ / k) := le_min le_rfl h1
    exact le_trans (le_of_lt ‹σ < 1›) hfull







end Catalog.NET73


