-- Prove2me | solution 1 for FHENoise.NoiseGauge.nu_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T05:31:17.677334+00:00
-- url     : https://prove2.me/submissions/b9d49ddd-8368-426a-976e-dbae58381fb1

-- Sol generated from Cryptography/FHE/NoiseGauge.lean
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














/-! ### Concrete gauge 1: the integers -/




/-! ### Concrete gauge 2: the `ℓ¹` norm on a convolution (group) algebra

`AddMonoidAlgebra ℤ A` for an additive commutative group `A` is the ring of
`ℤ`-valued functions on `A` under convolution; taking `A = ZMod n` gives
`ℤ[X]/(Xⁿ - 1)`, the negacyclic sibling of the cyclotomic rings used by BGV/BFV.
The `ℓ¹` coefficient norm is submultiplicative there, i.e. the expansion factor
is `1`. -/


variable {A : Type*}















open FHENoise.NoiseGauge in
theorem solution{ι : Type*} (s : Finset ι) (f : ι → R) :
    G.nu (∑ i ∈ s, f i) ≤ ∑ i ∈ s, G.nu (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [G.nu_zero]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact le_trans (G.nu_add_le _ _) (by linarith)
