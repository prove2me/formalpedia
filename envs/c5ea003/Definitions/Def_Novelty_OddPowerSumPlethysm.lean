-- Prove2me | Definitions.Def_Novelty_OddPowerSumPlethysm
-- name    : Novelty_OddPowerSumPlethysm
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:33:59.193754+00:00
-- url     : https://prove2.me/theorems/de279b8c-bae3-4ce1-8aa7-3abb628aa570
-- title:
--   Aether Catalog definitions — Novelty_OddPowerSumPlethysm
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.OddPowerSumPlethysm`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/OddPowerSumPlethysm.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The odd power-sum plethysm `φ_t : p_n ↦ (1 - t^n) p_n` as an automorphism

This companion file isolates the *abstract* plethystic operator
`φ_t : p_{2k+1} ↦ (1 - t^{2k+1}) p_{2k+1}` on the ring of odd power-sum symmetric
functions, modeled as `Lam = MvPolynomial ℕ K` over `K = ℚ(t)` (variable `X k = p_{2k+1}`),
independently of the Schur-`Q` / vertex-operator machinery used in
`PlethysticTrivialityShiftedTSchur`.

The "plethystic triviality" of the shifted `t`-Schur basis is, at bottom, a statement
about `φ_t` alone: it is an algebra automorphism that is *diagonal in the monomial basis*
and *degree-preserving*, yet genuinely non-trivial (not the identity).  These three facts
are the structural reason the `t`-deformation is a mere invertible relabelling.

Main results:
* `phiTEquiv` / `phiT_bijective` — `φ_t` is an algebra automorphism with inverse
  `ψ_t : p_n ↦ p_n / (1 - t^n)`.
* `phiT_monomial_pow` — `φ_t` is *diagonal* on each variable-power: `φ_t(p_n^m) =
  (1 - t^n)^m p_n^m`.
* `phiT_isHomogeneous` — `φ_t` preserves the grading by total degree.
* `phiT_X_zero_ne` / `phiT_ne_id` — `φ_t` is genuinely non-trivial (`φ_t ≠ id`), so
  "triviality" means *automorphic*, not *identity* (the Critic's boundary check).

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer):  The whole `S^t` vs `Q` story is governed by a single linear
  operator `φ_t` that is diagonal in the monomial basis; thus the deformation must
  preserve every grading-respecting structural invariant.
Experiment (Experimenter):  Prove `φ_t(X k ^ m) = C(cc k ^ m) * X k ^ m` by `map_pow`
  and `phiT_X`; lift to homogeneity via `MvPolynomial.IsHomogeneous.aeval` with each
  generator `C (cc k) * X k` homogeneous of degree `1` (`isHomogeneous_C_mul_X`).
Analysis (Analyst):  Degree preservation is the abstract shadow of `|S^t_λ| = |λ| = |Q_λ|`:
  the plethysm never mixes degrees, only rescales monomials by `∏ (1 - t^{n_i})`.
Critique (Critic):  A "trivial" basis change could be vacuously the identity; we refute
  this with `phiT_ne_id`, using `cc 0 = 1 - t ≠ 1` because `t = RatFunc.X ≠ 0`.
Synthesis (PI):  `φ_t` is a degree-preserving, monomial-diagonal automorphism — exactly
  the operator-theoretic content of plethystic triviality.
-- !-- end Lab Notes -- !--
-/

open MvPolynomial

noncomputable section

namespace OddPowerSumPlethysm

/-- The base field `K = ℚ(t)`. -/
abbrev K := RatFunc ℚ

/-- The odd power-sum ring `MvPolynomial ℕ K`, with `X k` standing for `p_{2k+1}`. -/
abbrev Lam := MvPolynomial ℕ K

/-- The transcendental parameter `t ∈ K`. -/
def tt : K := RatFunc.X

/-- The scalar `c_k = 1 - t^{2k+1}`. -/
def cc (k : ℕ) : K := 1 - tt ^ (2 * k + 1)

lemma cc_ne (k : ℕ) : cc k ≠ 0 := by
  by_contra h_contra
  have h_eq : (1 - (RatFunc.X : RatFunc ℚ) ^ (2 * k + 1)) = 0 := by
    exact h_contra
  convert absurd h_eq ?_
  rw [ show ( 1 - RatFunc.X ^ ( 2 * k + 1 ) : RatFunc ℚ ) = algebraMap ( Polynomial ℚ ) ( RatFunc ℚ ) ( 1 - Polynomial.X ^ ( 2 * k + 1 ) ) by simp +decide, IsFractionRing.to_map_eq_zero_iff ]
  exact ne_of_apply_ne ( Polynomial.eval 0 ) ( by norm_num )

/-- The inverse scalar `1 / (1 - t^{2k+1})`. -/
def dd (k : ℕ) : K := 1 / cc k

/-- The plethystic endomorphism `φ_t : p_{2k+1} ↦ (1 - t^{2k+1}) p_{2k+1}`. -/
def phiT : Lam →ₐ[K] Lam :=
  MvPolynomial.aeval (fun k => MvPolynomial.C (cc k) * X k)

/-- The inverse plethystic endomorphism `ψ_t : p_{2k+1} ↦ p_{2k+1} / (1 - t^{2k+1})`. -/
def psiT : Lam →ₐ[K] Lam :=
  MvPolynomial.aeval (fun k => MvPolynomial.C (dd k) * X k)

@[simp] lemma phiT_X (k : ℕ) : phiT (X k) = MvPolynomial.C (cc k) * X k := by
  simp [phiT]

@[simp] lemma psiT_X (k : ℕ) : psiT (X k) = MvPolynomial.C (dd k) * X k := by
  simp [psiT]

/-- `ψ_t` is a left inverse of `φ_t`. -/
lemma psiT_phiT : psiT.comp phiT = AlgHom.id K Lam := by
  ext x
  simp +decide [ phiT, psiT ]
  simp +decide [ dd, cc_ne ]

/-- `ψ_t` is a right inverse of `φ_t`. -/
lemma phiT_psiT : phiT.comp psiT = AlgHom.id K Lam := by
  ext x
  simp +decide [ dd, cc_ne ]

/-- **`φ_t` is an algebra automorphism** of the odd power-sum ring. -/
def phiTEquiv : Lam ≃ₐ[K] Lam :=
  AlgEquiv.ofAlgHom phiT psiT phiT_psiT psiT_phiT


/-
`φ_t` is bijective.
-/

/-! ### `φ_t` is diagonal in the monomial basis -/

/-
`φ_t` scales each variable-power diagonally: `φ_t(p_n^m) = (1 - t^n)^m p_n^m`.
-/

/-! ### `φ_t` preserves the grading -/

/-
**`φ_t` is degree-preserving**: it maps homogeneous polynomials of degree `m` to
homogeneous polynomials of degree `m`.
-/

/-! ### Non-triviality boundary (the deformation is real) -/

/-
`φ_t` genuinely moves `p_1`: `φ_t(p_1) = (1 - t) p_1 ≠ p_1`.
-/

/-
**`φ_t` is not the identity.**  "Plethystic triviality" therefore means *automorphic*,
not *identity*: the `t`-deformation is a genuine, invertible relabelling.
-/

end OddPowerSumPlethysm


