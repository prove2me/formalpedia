-- Prove2me | Definitions.Def_Cryptography_LogisticMapChaos
-- name    : Cryptography_LogisticMapChaos
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T02:19:42.697348+00:00
-- url     : https://prove2.me/theorems/65ae7dcc-b427-48a4-a733-78f2a351c488
-- title:
--   Aether Catalog definitions — Cryptography_LogisticMapChaos
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.LogisticMapChaos`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/LogisticMapChaos.lean by skeleton subtraction
import Mathlib

/-!
# Chaos as a keystream: the logistic map at full strength

The **logistic map** `f(x) = 4·x·(1 - x)` on the unit interval is the archetypal
one-dimensional chaotic system.  A chaos-based stream cipher uses the orbit
`x₀, f(x₀), f²(x₀), …` of a secret seed `x₀ ∈ (0,1)` as a keystream: the plaintext
is masked by successive iterates.  The security folklore rests on two structural
claims about `f`:

* **Sensitivity** — two seeds that are exponentially close become macroscopically
  separated after only linearly many iterations (this is the "avalanche" a cipher
  needs); and
* **Algebraic depth** — the `n`-th iterate `fⁿ` is a polynomial of degree `2ⁿ`, so
  recovering the seed from the keystream means solving an equation whose degree is
  exponential in the number of steps.

This file makes both statements precise and proves them.  The unifying device is
the exact **semiconjugacy of the logistic map to angle doubling**:

  `f(sin² t) = sin²(2 t)`,      hence      `fⁿ(sin² t) = sin²(2ⁿ t)`.

Under the substitution `x = sin² t` the logistic dynamics becomes the doubling
map `t ↦ 2 t`, whose exponential stretching factor `2ⁿ` is exactly the source of
both the sensitivity and the degree growth.  The Lyapunov exponent `log 2` is the
logarithm of that per-step factor.

## Main results

* `LogisticChaos.logistic_maps_unitInterval` — `f` maps `[0,1]` into itself.
* `LogisticChaos.logistic_fixedPoints` — the only real fixed points are `0` and `3/4`.
* `LogisticChaos.logistic_conjugacy` — `f(sin² t) = sin²(2 t)`.
* `LogisticChaos.logistic_iterate_conjugacy` — `fⁿ(sin² t) = sin²(2ⁿ t)`.
* `LogisticChaos.logisticPoly_iterate_natDegree` — the `n`-th iterate is a
  polynomial of degree `2ⁿ`.
* `LogisticChaos.logisticPoly_iterate_eval` — the polynomial iterate evaluates to
  the functional iterate.
* `LogisticChaos.sensitivity` — an explicit family of seeds collapsing to `0`
  whose `n`-th iterates stay a fixed distance `1/2` from the orbit of `0`,
  the quantitative form of sensitive dependence on initial conditions.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer).  "Chaos is cryptography": the logistic map at `r = 4`
should exhibit (i) exponential sensitivity to the seed and (ii) an `n`-th iterate
of algebraic degree `2ⁿ`, the two ingredients a stream cipher advertises.

Experiment (Experimenter).  Rather than attack floating-point orbits, we work
exactly.  The identity `4 sin²t cos²t = sin²(2t)` conjugates `f` to angle
doubling; a clean induction lifts it to all iterates, giving both the `2ⁿ`
stretching and — via `Polynomial.natDegree_comp` — the `2ⁿ` algebraic degree.
Sensitivity is exhibited concretely: the seeds `sin²(π/2ⁿ⁺²)` shrink to `0`, yet
after `n` steps each lands exactly on `1/2` (because `2ⁿ·π/2ⁿ⁺² = π/4`), a fixed
gap from the orbit of the fixed point `0`.

Analysis (Analyst).  The doubling picture explains *why* the naive "chaos cipher"
is both attractive and fragile.  Attractive: the `2ⁿ` degree makes algebraic seed
recovery look exponential.  Fragile: conjugacy to `t ↦ 2t (mod 1)` is exactly the
binary shift map, so in binary the keystream merely reads off the bits of `t` —
transparent to anyone who thinks in the conjugate coordinate.  Sensitivity is
real but is a double-edged sword shared by the cryptanalyst.

Critique (Critic).  We avoid vacuity: `logistic_fixedPoints` is an iff pinning the
fixed set to `{0, 3/4}`; `sensitivity` produces genuinely distinct, converging
seeds with a constant output gap; the degree theorem is proved through polynomial
composition, not by fiat.  No result is `True`-typed or a definitional rfl.

Synthesis (PI).  The exact conjugacy `fⁿ(sin²t) = sin²(2ⁿt)` is the single
structural fact from which sensitivity (dynamics) and degree `2ⁿ` (algebra) both
flow — a concrete bridge between real dynamics and polynomial algebra.
-/

namespace LogisticChaos

open Polynomial

/-- The logistic map at the fully chaotic parameter `r = 4`. -/
def logistic (x : ℝ) : ℝ := 4 * x * (1 - x)





/-! ## Semiconjugacy to angle doubling -/




/-! ## Algebraic depth: the `n`-th iterate has degree `2ⁿ` -/

/-- The logistic map as a real polynomial. -/
noncomputable def logisticPoly : Polynomial ℝ := C 4 * X * (1 - X)

/-- The `n`-fold composition of `logisticPoly` with itself
(`compIter 0 = X`, the identity polynomial). -/
noncomputable def logisticPolyIter : ℕ → Polynomial ℝ
  | 0 => X
  | (n + 1) => logisticPoly.comp (logisticPolyIter n)




/-! ## Sensitive dependence on initial conditions -/

/-- The sensitivity seeds `sₙ = sin²(π/2ⁿ⁺²)`, converging to the fixed point `0`. -/
noncomputable def sensSeed (n : ℕ) : ℝ := Real.sin (Real.pi / 2 ^ (n + 2)) ^ 2





end LogisticChaos


