-- Prove2me | Definitions.Def_MachineLearning_PRNGSeedRecoveryLFSR
-- name    : MachineLearning_PRNGSeedRecoveryLFSR
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T18:49:37.778768+00:00
-- url     : https://prove2.me/theorems/387037c4-cafa-421b-8449-da8858bb335d
-- title:
--   Aether Catalog definitions — MachineLearning_PRNGSeedRecoveryLFSR
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.PRNGSeedRecoveryLFSR`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/PRNGSeedRecoveryLFSR.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Seed Recovery for Linear Feedback Shift Registers

This module formalises the mathematical core of *seed recovery* for the LFSR
family of pseudo-random generators, the first half of the "detect PRNG output
and replace the file by its seed" programme (see
`MachineLearning.PRNGCompressionBound` for the counting-side limits).

An LFSR of order `L` over a commutative ring `F` with tap vector
`c : Fin L → F` produces a stream `x : ℕ → F` obeying

  `x (n + L) = ∑ i < L, c i * x (n + i)`.

## Main results

* `lfsrRun` — the generator: run the register from an explicit seed.
* `lfsrRun_isLinRec`, `lfsrRun_of_lt` — the generator does what it claims.
* `IsLinRec.ext_of_agree` — **rigidity**: two streams with the same taps that
  agree on one window of length `L` agree forever.
* `IsLinRec.seed_recovery` — **the falsifiability gate**: any stream obeying the
  recurrence is *exactly* reproduced by re-running the register from its own
  first `L` symbols.  Nothing beyond the seed has to be stored.
* `linRec_taps_unique_of_span` — **Berlekamp–Massey uniqueness**: if the first
  `L` state windows span `F^L`, the tap vector is uniquely determined by the
  stream, so seed recovery has a unique answer.
* `hankel_span_of_taps_unique` — the converse over a field: tap uniqueness
  forces the windows to span.  Spanning is therefore *exactly* the right
  nondegeneracy condition.

## Application keywords

LFSR, linear recurrence, Berlekamp–Massey, seed recovery, PRNG fingerprinting,
stream compression
-/


open Finset

namespace PRNGSeed

section Ring

variable {F : Type*} [CommRing F]

/-- `IsLinRec L c x` : the stream `x` obeys the order-`L` linear recurrence with
tap vector `c`, i.e. it is an output stream of the corresponding LFSR. -/
def IsLinRec (L : ℕ) (c : Fin L → F) (x : ℕ → F) : Prop :=
  ∀ n : ℕ, x (n + L) = ∑ i : Fin L, c i * x (n + i)

/-- Run the length-`L` shift register with taps `c` from the seed `init`. -/
def lfsrRun {L : ℕ} (c init : Fin L → F) : ℕ → F
  | n =>
    if h : n < L then init ⟨n, h⟩
    else ∑ i : Fin L, c i * lfsrRun c init (n - L + (i : ℕ))
  decreasing_by
    have hi := i.isLt
    omega

variable {L : ℕ} {c init : Fin L → F}








/-! ### Periodic data is seed-compressible -/

/-- The tap vector `(1, 0, …, 0)`: the register that simply repeats its seed. -/
def unitTap (p : ℕ) : Fin p → F := fun i => if (i : ℕ) = 0 then 1 else 0




/-- The state window of the stream `x` starting at time `n`. -/
def window (x : ℕ → F) (L n : ℕ) : Fin L → F := fun i => x (n + (i : ℕ))


end Ring

section Uniqueness

variable {F : Type*} [Field F] {L : ℕ} {x : ℕ → F}

/-- The subspace of `F^L` spanned by all state windows of the stream `x`. -/
def windowSpan (x : ℕ → F) (L : ℕ) : Submodule F (Fin L → F) :=
  Submodule.span F (Set.range fun n : ℕ => window x L n)


/-- The dot product functional attached to a coefficient vector. -/
def dotL (e : Fin L → F) : (Fin L → F) →ₗ[F] F where
  toFun v := ∑ i : Fin L, e i * v i
  map_add' v w := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' a v := by
    simp [Finset.mul_sum, mul_left_comm]







end Uniqueness

end PRNGSeed


