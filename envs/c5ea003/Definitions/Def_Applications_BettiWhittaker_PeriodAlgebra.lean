-- Prove2me | Definitions.Def_Applications_BettiWhittaker_PeriodAlgebra
-- name    : Applications_BettiWhittaker_PeriodAlgebra
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:36:20.915226+00:00
-- url     : https://prove2.me/theorems/41027478-cede-4950-9976-5ca9a1aea147
-- title:
--   Aether Catalog definitions — Applications_BettiWhittaker_PeriodAlgebra
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.BettiWhittaker.PeriodAlgebra`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/BettiWhittaker/PeriodAlgebra.lean by skeleton subtraction
import Mathlib
/-
# The algebra of the Betti–Whittaker contragredient period relation, and a self-dual obstruction

This file isolates the **algebraic content** of the contragredient period relation
(companion: `NumberTheory/BettiWhittakerContragredientFormal.lean` and the sign analysis in
`Applications/BettiWhittaker/BottomDegreeParity.lean`):

  `p^b(π∨) = (-1)^{b(F,n)} · p^b(π)`,    `b(F,n) = r₁·⌊n²/4⌋ + r₂·n(n-1)/2`.

Working with the periods as honest nonzero complex numbers, we extract three facts that hold for
*any* sign `s` and then specialise to `s = (-1)^{b(F,n)}`:

* **Consistency** (`relation_involutive_forces_sq`): because the contragredient is an involution
  (`(π∨)∨ = π`), applying the relation twice forces `s² = 1`.  The square-root-of-unity property
  of the sign is therefore not an extra hypothesis — it is *forced* by the relation.
* **Self-dual compatibility** (`selfDual_compatible_iff`): for a fixed nonzero period the relation
  is compatible with self-duality `π ≅ π∨` (i.e. `p∨ = p`) **iff** `s = 1`.
* **Self-dual obstruction** (`no_selfDual_of_odd`, `selfDual_iff_even_bDeg`): consequently a
  generic cohomological representation with a nonzero bottom Betti–Whittaker period can be
  self-dual **only when `b(F,n)` is even**.  When `b(F,n)` is odd the sign is `-1` and self-duality
  is impossible.  Combined with the `n mod 4` parity trichotomy of the companion file, this turns
  into explicit congruence conditions on `(n, r₁, r₂)`.

The file is self-contained (`import Mathlib`); it reuses the bottom degree `bDeg` (matching the
companion files) inside the dedicated namespace `BettiWhittaker.Period`.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): the period sign is not free — involutivity of `π ↦ π∨` should pin down
`s² = 1`, and a *self-dual* `π` should be obstructed whenever the sign is `-1`.  Bold sub-claim:
self-duality is impossible precisely in the odd-`b(F,n)` degrees.

Experiment (Experimenter): modelled the periods as `p, q : ℂ` with `q = s·p`.  Proved
`s² = 1` from `q = s·p` together with the involution `p = s·q` (one `linear_combination`).  Proved
`q = p ↔ s = 1` for `p ≠ 0` by factoring `(s-1)·p = 0`.

Analysis (Analyst): the obstruction is *clean* — it needs only `p ≠ 0` and the relation, no
analytic input.  The arithmetic enters solely through the parity of `b(F,n)`.  Failure mode that
was ruled out: trying to phrase everything in the unit group `ℂˣ` introduced a missing `Neg`
instance; switching to `ℂ` with an explicit `p ≠ 0` hypothesis is cleaner and strictly more
general (it also covers the degenerate `p = 0` case as "no constraint").

Critique (Critic): is `no_selfDual_of_odd` vacuous (could `p` be forced to `0`)?  No — it is a
genuine `q ≠ p` conclusion under `p ≠ 0`.  Adversarial counterexample: if `b(F,n)` is *even* the
obstruction must fail, and indeed `selfDual_iff_even_bDeg` shows self-duality is then permitted —
so the boundary is exactly the parity of `b(F,n)`, not an artefact.

Synthesis (PI): the sign is a forced square root of unity; self-duality lives exactly in the
even-degree locus; oddness is a hard obstruction.
-/

namespace BettiWhittaker.Period

/-! ## The abstract period relation -/





/-! ## The concrete sign `(-1)^{b(F,n)}` and the self-dual obstruction -/

/-- The bottom cohomological degree `b(F,n) = r₁·⌊n²/4⌋ + r₂·n(n-1)/2` (matching the companion
catalog files). -/
def bDeg (n r₁ r₂ : ℕ) : ℕ := r₁ * (n / 2) * ((n + 1) / 2) + r₂ * n * (n - 1) / 2

/-- The contragredient sign as a complex number, `(-1)^{b(F,n)} ∈ ℂ`. -/
noncomputable def contraSignC (n r₁ r₂ : ℕ) : ℂ := (-1) ^ bDeg n r₁ r₂






end BettiWhittaker.Period


