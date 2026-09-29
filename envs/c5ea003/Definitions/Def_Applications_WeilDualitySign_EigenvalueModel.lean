-- Prove2me | Definitions.Def_Applications_WeilDualitySign_EigenvalueModel
-- name    : Applications_WeilDualitySign_EigenvalueModel
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:57:22.790128+00:00
-- url     : https://prove2.me/theorems/f5a51746-f6c2-434a-abe5-642a50e9bc21
-- title:
--   Aether Catalog definitions — Applications_WeilDualitySign_EigenvalueModel
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.WeilDualitySign.EigenvalueModel`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/WeilDualitySign/EigenvalueModel.lean by skeleton subtraction
import Mathlib
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

namespace WeilDualitySign

/-- A **duality eigensystem**: the axiomatised eigenvalue model of the middle cohomology
of a variety over a finite field.  `Q` plays the role of `q^{n/2}`, `α` is the family of
Frobenius eigenvalues, and `σ` is the duality permutation, an involution pairing `α i`
with `α (σ i)` into the Tate twist `Q² = q^n`. -/
structure DualEigensystem (K : Type*) [Field K] (ι : Type*) [Fintype ι] [DecidableEq ι]
    where
  /-- The half-weight scalar `Q = q^{n/2}`. -/
  Q : K
  /-- `Q` is invertible. -/
  Q_ne_zero : Q ≠ 0
  /-- The Frobenius eigenvalues. -/
  α : ι → K
  /-- The duality permutation. -/
  σ : Equiv.Perm ι
  /-- Duality is an involution. -/
  σ_involutive : ∀ i, σ (σ i) = i
  /-- Poincaré duality: paired eigenvalues multiply to `q^n = Q²`. -/
  duality : ∀ i, α i * α (σ i) = Q ^ 2

namespace DualEigensystem

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (E : DualEigensystem K ι)

/-- The **degree** of the system: the number of eigenvalues, i.e. the Betti number. -/
def deg (_E : DualEigensystem K ι) : ℕ := Fintype.card ι


/-- The set of **anti-diagonal fixed points**: indices fixed by duality whose eigenvalue
is `−Q` (rather than `+Q`). -/
noncomputable def negFixed : Finset ι := by
  classical
  exact univ.filter (fun i => E.σ i = i ∧ E.α i = -E.Q)


/-! ### Elementary structure -/



/-! ### The pairing cancellation -/

/-- The normalised eigenvalues `β i = α i / Q`, with the fixed points neutralised to `1`.
This is the auxiliary function on which duality acts as a free involution. -/
noncomputable def normNonFixed (i : ι) : K := by
  classical
  exact if E.σ i = i then 1 else E.α i / E.Q


/-! ### The sign law -/




/-! ### The functional equation and its sign -/

/-- The characteristic polynomial `P(T) = ∏ (1 - α_i T)` of the eigenvalue system,
as a function of `T`. -/
def charPoly (T : K) : K := ∏ i, (1 - E.α i * T)


/-- **The root sign of the functional equation** in the eigenvalue model:
`ε = (−1)^d · (∏ α_i) / Q^d`. -/
noncomputable def rootSign : K := (-1 : K) ^ E.deg * (∏ i, E.α i) / E.Q ^ E.deg





end DualEigensystem

end WeilDualitySign


