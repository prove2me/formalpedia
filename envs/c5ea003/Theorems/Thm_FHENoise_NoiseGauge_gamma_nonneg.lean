-- Prove2me | Theorems.Thm_FHENoise_NoiseGauge_gamma_nonneg
-- name    : FHENoise.NoiseGauge.gamma_nonneg
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T02:48:52.513444+00:00
-- url     : https://prove2.me/theorems/877bb7aa-9e0e-42fd-b047-a6e841d84865
-- title:
--   Gamma nonneg
-- statement:
--   Formal statement of `FHENoise.NoiseGauge.gamma_nonneg` from the Aether Catalog (Cryptography). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem FHENoise.NoiseGauge.gamma_nonneg: 0 ≤ G.gamma := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/FHE/NoiseGauge.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/FHE/NoiseGauge.lean#L54

-- Thm stub generated from Cryptography/FHE/NoiseGauge.lean
import Mathlib
import Definitions.Def_Cryptography_FHE_NoiseGauge

/-!
# Noise gauges: the analytic layer of FHE noise accounting

A *noise gauge* on a commutative ring `R` is a subadditive, symmetric,
submultiplicative-up-to-an-expansion-factor size function `ν : R → ℝ`.  It
abstracts the canonical/coefficient norms used in BGV/BFV noise analysis:

* `R = ℤ` with `ν = |·|` and expansion factor `γ = 1`;
* `R = ℤ[X]/(X^n - 1)` (a group algebra) with the `ℓ¹` coefficient norm and
  `γ = 1`;
* the same ring with the `ℓ^∞` norm and `γ = n` (the classical *ring expansion
  factor* `δ_R`).

Everything downstream (noise growth of homomorphic addition, multiplication,
relinearization, modulus switching, bootstrapping) is proved once and for all at
this level of generality, so it applies verbatim to every concrete instance.

Main definitions and results of this file:

* `FHENoise.NoiseGauge` — the structure itself;
* `NoiseGauge.nu_sub_le`, `nu_sum_le` — subadditivity, including over `Finset`s;
* `NoiseGauge.gamma_nu_pow_le` — `γ · ν (x ^ n) ≤ (γ · ν x) ^ n` for `n ≥ 1`,
  the multiplicative-depth engine;
* `FHENoise.intGauge` — the integer instance;
* `FHENoise.l1Gauge` — the `ℓ¹` gauge on a commutative group algebra
  `AddMonoidAlgebra ℤ A`, i.e. on cyclotomic-style convolution rings.
-/

open FHENoise

open Finset BigOperators


open NoiseGauge

variable {R : Type*} [CommRing R] (G : NoiseGauge R)

theorem FHENoise.NoiseGauge.gamma_nonneg: 0 ≤ G.gamma := by sorry
