-- Prove2me | Definitions.Def_Bridges_MatsunoIwasawaMonoidHom
-- name    : Bridges_MatsunoIwasawaMonoidHom
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:29:15.881815+00:00
-- url     : https://prove2.me/theorems/7c85dfb9-7be9-42ed-9fd6-86357fc3f913
-- title:
--   Aether Catalog definitions — Bridges_MatsunoIwasawaMonoidHom
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.MatsunoIwasawaMonoidHom`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/MatsunoIwasawaMonoidHom.lean by skeleton subtraction
import Mathlib

/-!
# The Iwasawa invariant pair as a monoid homomorphism: a bridge to valuation theory

## Overview

This file *deepens* the algebraic model of the two classical **Iwasawa invariants**
`μ` and `λ` of a characteristic element built in `MatsunoIwasawaBridge.lean`.  There,
for `f = Σ aᵢ Xⁱ ∈ ℤ[X]` one sets

* `μ_p(f) = padicValInt p (content f)` — the least `p`-adic valuation of a coefficient
  (a `ℤ`-arithmetic / commutative-algebra datum), and
* `λ_p(f) = natTrailingDegree (reduce_p (primPart f))` — the first index at which that
  minimum is attained (a `𝔽_p[X]` combinatorial datum),

and proved that both are **additive under multiplication**.

Here we go one structural level higher and package this additivity as a genuine
**cross-domain bridge**:

1. **Monoid homomorphism (`iwasawaHom`).**  The pair `f ↦ (μ_p f, λ_p f)` is a
   *monoid homomorphism* from the multiplicative monoid `ℤ[X]⁰` of nonzero integer
   polynomials to the additive monoid `ℕ × ℕ` (viewed multiplicatively).  This is
   the precise statement that the Iwasawa invariants define a **valuation-type
   object**: an additive invariant of the multiplicative structure, connecting
   number theory (Iwasawa `μ`, `λ`) with the algebra of ordered monoids.

2. **Divisibility monotonicity (`muInv_le_of_dvd`, `lambdaInv_le_of_dvd`).**  Both
   invariants are *monotone under divisibility* — the hallmark of a valuation.  This
   bridges the **ring-theoretic** divisibility order on `ℤ[X]` with the numerical
   order on the invariants.

3. **`λ` = order of vanishing at `0` (`lambdaInv_eq_rootMultiplicity`).**  The
   `λ`-invariant literally equals `rootMultiplicity 0` of the reduced primitive part,
   i.e. the **order of vanishing at the origin** of the mod-`p` reduction.  This
   connects Iwasawa theory to the local (algebro-geometric) notion of multiplicity of
   a root.

4. **Finite-product formulas (`muInv_prod`, `lambdaInv_prod`).**  Both invariants
   turn a finite product of characteristic elements into a finite sum of invariants —
   the Iwasawa invariant of a product of many characteristic elements.

5. **Iterated Matsuno twist (`matsuno_iterated_twist`).**  Twisting a characteristic
   element by a family of twist factors shifts the `λ`-invariant by the sum of the
   individual `μ`-proportional contributions.

All statements are self-contained and depend only on Mathlib.
-/

namespace IwasawaMonoidHom

open Polynomial BigOperators

variable (p : ℕ) [Fact p.Prime]

/-- Reduction of an integer polynomial modulo the prime `p`. -/
noncomputable def reduce (f : Polynomial ℤ) : Polynomial (ZMod p) :=
  f.map (Int.castRingHom (ZMod p))

/-- The **Iwasawa μ-invariant** of `f`: the `p`-adic valuation of its content. -/
noncomputable def muInv (f : Polynomial ℤ) : ℕ :=
  padicValInt p f.content

/-- The **Iwasawa λ-invariant** of `f`: the trailing degree of the mod-`p`
reduction of the primitive part of `f`. -/
noncomputable def lambdaInv (f : Polynomial ℤ) : ℕ :=
  (reduce p f.primPart).natTrailingDegree

/-! ### Base additivity facts (self-contained restatement of the bridge) -/

/-- Reduction is a ring homomorphism, hence multiplicative. -/
theorem reduce_mul (a b : Polynomial ℤ) : reduce p (a * b) = reduce p a * reduce p b :=
  Polynomial.map_mul _

/-- The reduction of a primitive polynomial modulo `p` is nonzero. -/
theorem reduce_primPart_ne_zero (f : Polynomial ℤ) :
    reduce p f.primPart ≠ 0 := by
  intro h
  have hprim : f.primPart.IsPrimitive := isPrimitive_primPart f
  have hall : ∀ i, (p : ℤ) ∣ f.primPart.coeff i := by
    intro i
    have hz : ((f.primPart.coeff i : ℤ) : ZMod p) = 0 := by
      have := congrArg (fun q => Polynomial.coeff q i) h
      simpa [reduce, Polynomial.coeff_map] using this
    rwa [ZMod.intCast_zmod_eq_zero_iff_dvd] at hz
  have hCd : C (p : ℤ) ∣ f.primPart := (C_dvd_iff_dvd_coeff _ _).2 hall
  have hu := hprim (p : ℤ) hCd
  have hp := (Fact.out : p.Prime)
  have hp2 : (2 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp.two_le
  rw [Int.isUnit_iff] at hu
  rcases hu with h1 | h1 <;> omega

/-- **μ is additive** (Gauss's lemma + additivity of the `p`-adic valuation). -/
theorem muInv_mul {f g : Polynomial ℤ} (hf : f ≠ 0) (hg : g ≠ 0) :
    muInv p (f * g) = muInv p f + muInv p g := by
  have hcf : f.content ≠ 0 := by rwa [Ne, content_eq_zero_iff]
  have hcg : g.content ≠ 0 := by rwa [Ne, content_eq_zero_iff]
  unfold muInv
  rw [content_mul, padicValInt.mul hcf hcg]

/-- **λ is additive** (additivity of the trailing degree in the domain `𝔽_p[X]`). -/
theorem lambdaInv_mul {f g : Polynomial ℤ} (hf : f ≠ 0) (hg : g ≠ 0) :
    lambdaInv p (f * g) = lambdaInv p f + lambdaInv p g := by
  have hfg : f * g ≠ 0 := mul_ne_zero hf hg
  unfold lambdaInv
  rw [primPart_mul hfg, reduce_mul,
    natTrailingDegree_mul (reduce_primPart_ne_zero p f) (reduce_primPart_ne_zero p g)]

/-! ### The invariants at the identity -/

omit [Fact p.Prime] in
/-- The `μ`-invariant of `1` is `0`. -/
theorem muInv_one : muInv p (1 : Polynomial ℤ) = 0 := by
  unfold muInv
  rw [content_one]
  simp [padicValInt]

/-- The `λ`-invariant of `1` is `0`. -/
theorem lambdaInv_one : lambdaInv p (1 : Polynomial ℤ) = 0 := by
  have hprim : (1 : Polynomial ℤ).primPart = 1 :=
    (Polynomial.isPrimitive_one).primPart_eq
  unfold lambdaInv reduce
  rw [hprim]
  simp

/-! ### `λ` as an order of vanishing (bridge to local multiplicity) -/


/-! ### Divisibility monotonicity (bridge to the divisibility order) -/



/-! ### Finite-product formulas -/



/-! ### The monoid homomorphism: the central cross-domain bridge -/

/-- **The Iwasawa invariant pair as a monoid homomorphism.**  The map
`f ↦ (μ_p f, λ_p f)` is a monoid homomorphism from the multiplicative monoid
`ℤ[X]⁰` of nonzero integer polynomials to the additive monoid `ℕ × ℕ` (viewed
multiplicatively).  This packages the additivity of both invariants as a single
structural statement, exhibiting the Iwasawa invariants as a **valuation-type**
homomorphism from a multiplicative structure (number theory) into an ordered
additive monoid (algebra). -/
noncomputable def iwasawaHom : (nonZeroDivisors (Polynomial ℤ)) →* Multiplicative (ℕ × ℕ) where
  toFun f := Multiplicative.ofAdd (muInv p (f : Polynomial ℤ), lambdaInv p (f : Polynomial ℤ))
  map_one' := by
    simp only [Submonoid.coe_one]
    rw [muInv_one, lambdaInv_one]
    rfl
  map_mul' a b := by
    have ha : (a : Polynomial ℤ) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.1 a.2
    have hb : (b : Polynomial ℤ) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.1 b.2
    simp only [Submonoid.coe_mul]
    rw [muInv_mul p ha hb, lambdaInv_mul p ha hb]
    rfl




/-! ### The Matsuno-type twist factor and its iteration -/

/-- The modelled quadratic-twist factor `p^k · X^(c·k)`. -/
noncomputable def twistFactor (c k : ℕ) : Polynomial ℤ :=
  C ((p : ℤ) ^ k) * X ^ (c * k)









/-! ### Worked numerical instances (machine-checked) -/

end IwasawaMonoidHom


