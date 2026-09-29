-- Prove2me | solution 1 for WeilDualitySign.DualEigensystem.charPoly_functional_equation
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:02:47.353381+00:00
-- url     : https://prove2.me/submissions/11640874-46c4-4e94-a733-04817d8256bc

-- Sol generated from Applications/WeilDualitySign/EigenvalueModel.lean
import Mathlib
import Definitions.Def_Applications_WeilDualitySign_EigenvalueModel
import Theorems.Thm_WeilDualitySign_DualEigensystem_deg_eq_card
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Eigenvalue Model of the Functional-Equation Sign

## The problem

For a smooth projective variety `X / 𝔽_q` of dimension `n`, the middle-degree factor of
the zeta function is a polynomial

  `P(T) = ∏_{i=1}^{d} (1 - α_i T)`,        `|α_i| = q^{n/2}`,

and **Poincaré duality** acts on the multiset of Frobenius eigenvalues by
`α ↦ q^n / α`.  Concretely there is a permutation `σ` of the index set with

  `α_i · α_{σ(i)} = q^n = Q²`,   `Q := q^{n/2}`.

Substituting `T ↦ 1/(Q² T)` in `P` produces the functional equation

  `(Q²T)^d · P((Q²T)⁻¹) = ε · Q^d · P(T)`,

whose **sign** `ε = ±1` is the arithmetic invariant of interest (it is the root number
of the associated `L`-factor, and by the parity philosophy of
`Catalog/Applications/BSD/FunctionalEquation.lean` it governs the parity of the order of
vanishing at the central point).

## What this file proves

The whole sign is controlled by the *fixed points* of the duality involution.  A fixed
point satisfies `α_i² = Q²`, hence `α_i = ±Q`; the mission conjecture is that forbidding
the value `α_i = −Q` at fixed points already forces

  `∏ α_i = Q^d = q^{nd/2}`,  hence  `ε = (−1)^d`.

We prove this, and more: the exact sign law

  `∏_i α_i = (−1)^{#{i : σ(i) = i ∧ α_i = −Q}} · Q^d`   (`prod_alpha_eq_sign_mul_pow`)

together with its sharp converse (`prod_alpha_eq_pow_iff_even`, over any field where
`−1 ≠ 1`): the conjectured conclusion holds **iff** the number of `−Q`-fixed points is
*even*.  The hypothesis "no `−Q` fixed point" is therefore sufficient but not necessary,
and the boundary is exactly a `ℤ/2` parity count of fixed points — a Lefschetz-style
statement.  Explicit witnesses in degrees `1, 2, 4` (see `Witnesses.lean`) show every
branch is realised.

## Honest scope

`DualEigensystem` is an *axiomatised model*: it records exactly the duality structure
(`σ` an involution with `α_i α_{σ i} = Q²`) that the Weil conjectures supply, over an
arbitrary field.  Nothing about the *existence* of such systems for actual varieties, nor
the Riemann-hypothesis bound `|α_i| = q^{n/2}`, is used or claimed — the results are
purely structural consequences of duality, and hence apply verbatim to any cohomological
setting with a perfect pairing into the Tate twist.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): the sign `ε` of a duality-symmetric eigenvalue system is
  *not* extra data — it is a `ℤ/2` invariant of the fixed-point set of `σ`, namely the
  parity of the number of fixed points carrying the "anti-diagonal" eigenvalue `−Q`.
Experiment (Experimenter): normalise `β_i := α_i / Q`, so duality reads
  `β_i β_{σ i} = 1`.  Kill the fixed points by hand (`β_i ↦ 1` there) and apply
  `Finset.prod_involution` to the resulting function: every genuine 2-cycle cancels,
  and `∏ β_i` collapses to the product over `Fix(σ)`, which is a product of `±1`.
Analysis (Analyst): the failed naive route is squaring — `(∏ α_i)² = Q^{2d}` follows in
  one line from `σ` being a bijection, but it only determines `∏ α_i` up to sign, which
  is precisely the content at stake.  The involution/pairing argument is what breaks the
  ambiguity, and it genuinely needs `σ ∘ σ = id`: a mere bijection with
  `α_i α_{σ i} = Q²` is not enough (see the 4-cycle witness in `Witnesses.lean`).
Critique (Critic): "no `−Q` fixed point" is sufficient but *not* necessary — two `−Q`
  fixed points cancel, so the honest theorem is the parity statement
  `prod_alpha_eq_pow_iff_even`, which also needs `−1 ≠ 1` (in characteristic 2 the sign
  question is empty, and indeed the iff carries that hypothesis).
Synthesis (PI): the conjecture is TRUE, and it is the shadow of the exact law
  `ε = (−1)^{d + #neg-fixed}`; the `d = 1` witnesses show both signs occur, so no
  hypothesis can be dropped.
-/

open Finset

open WeilDualitySign


open DualEigensystem

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (E : DualEigensystem K ι)





/-! ### Elementary structure -/



/-! ### The pairing cancellation -/



/-! ### The sign law -/




/-! ### The functional equation and its sign -/










open WeilDualitySign.DualEigensystem in
theorem solution(T : K) (hT : T ≠ 0) :
    (E.Q ^ 2 * T) ^ E.deg * E.charPoly ((E.Q ^ 2 * T)⁻¹)
      = (-1 : K) ^ E.deg * (∏ i, E.α i) * E.charPoly T := by
  have hQT : E.Q ^ 2 * T ≠ 0 := mul_ne_zero (pow_ne_zero 2 E.Q_ne_zero) hT
  have hcancel : (E.Q ^ 2 * T) * (E.Q ^ 2 * T)⁻¹ = 1 := mul_inv_cancel₀ hQT
  have hpt : ∀ i : ι, (E.Q ^ 2 * T) * (1 - E.α i * (E.Q ^ 2 * T)⁻¹)
      = (-E.α i) * (1 - E.α (E.σ i) * T) := by
    intro i
    linear_combination (-E.α i) * hcancel - T * E.duality i
  have hnegprod : ∏ i, (-E.α i) = (-1 : K) ^ E.deg * ∏ i, E.α i := by
    calc ∏ i, (-E.α i) = ∏ i, ((-1 : K) * E.α i) := by simp
      _ = (-1 : K) ^ E.deg * ∏ i, E.α i := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, deg_eq_card]
  rw [charPoly, charPoly]
  calc (E.Q ^ 2 * T) ^ E.deg * ∏ i, (1 - E.α i * (E.Q ^ 2 * T)⁻¹)
      = ∏ i, ((E.Q ^ 2 * T) * (1 - E.α i * (E.Q ^ 2 * T)⁻¹)) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, deg_eq_card]
    _ = ∏ i, ((-E.α i) * (1 - E.α (E.σ i) * T)) := Finset.prod_congr rfl fun i _ => hpt i
    _ = (∏ i, (-E.α i)) * ∏ i, (1 - E.α (E.σ i) * T) := Finset.prod_mul_distrib
    _ = ((-1 : K) ^ E.deg * ∏ i, E.α i) * ∏ i, (1 - E.α i * T) := by
        rw [Equiv.prod_comp E.σ (fun j => 1 - E.α j * T), hnegprod]
    _ = (-1 : K) ^ E.deg * (∏ i, E.α i) * ∏ i, (1 - E.α i * T) := by ring
