-- Prove2me | Definitions.Def_ErdosProblems_Erdos269_RestrictedFloorSum
-- name    : ErdosProblems_Erdos269_RestrictedFloorSum
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-27T18:12:12.891749+00:00
-- url     : https://prove2.me/theorems/d916803a-0218-46fb-a41e-0d2b82b54b2d
-- title:
--   RestrictedFloorSum
-- statement:
--   Defines strict three-prime smooth counts and shells, pair projections, explicit exponent fibers and logarithmic floor sums. It also defines integer window products, forcing sums, and the cofinal local-window escape predicate.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/ErdosProblems/Erdos269/RestrictedFloorSum.lean#L1-L683
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/269/erdos-269-three-prime-running-lcm.tex#L1-L260
--   Paper prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/269/erdos-269-three-prime-running-lcm.tex#L681-L689

import Definitions.Def_ErdosProblems_Erdos269_ResidueEscape
import Definitions.Def_ErdosProblems_Erdos269_ThreePrimeRunningLcm
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Erdős #269: restricted floor sums and local windows

Problem-owned landing surface for the exact true-shell floor sums and the
local-window residue reduction.  No declaration here asserts the open
cofinal anti-concentration theorem.
-/

namespace ErdosProblems.Erdos269

open scoped BigOperators

/-! ## Exact finite strict counts -/

/-- Strict `{p,q,r}`-smooth exponent prefix.  The ambient exponent box of
side `x` is deliberately redundant; it gives a finite, integer-only carrier
for the strict inequality used by the returned floor-sum formula. -/
def strictSmoothExponents (p q r x : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((Finset.range x).product ((Finset.range x).product (Finset.range x))).filter
    fun e => smooth3Val p q r e.1 e.2.1 e.2.2 < x

/-- Exact strict smooth-number count in the finite exponent model. -/
def smoothCountLT (p q r x : ℕ) : ℕ :=
  (strictSmoothExponents p q r x).card





/-- Exact shell between two strict cutoffs. -/
def strictSmoothShell (p q r x y : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  strictSmoothExponents p q r y \ strictSmoothExponents p q r x



/-- Restricted count at a pure `p`-power cutoff.  This is the integer carrier
whose two-dimensional floor-sum evaluation is the next formalization seam. -/
def restrictedPurePowerCount (p q r a : ℕ) : ℕ :=
  smoothCountLT p q r (p ^ a)



/-! ## Exact two-dimensional fiber formula -/

/-- The admissible `(q,r)` exponent pairs below a strict cutoff.  Once such
a pair is fixed, only the remaining `p`-exponent has to be counted. -/
def strictSmoothPairs (q r x : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range x).product (Finset.range x)).filter
    fun e => q ^ e.1 * r ^ e.2 < x



/-- The restricted two-dimensional fiber sum: for every admissible `(q,r)`
pair, count exactly the `p`-exponents that keep the smooth value below `x`.
This is an integer-only version of the returned restricted floor sum. -/
def restrictedFiberCount (p q r x : ℕ) : ℕ :=
  ∑ e ∈ strictSmoothPairs q r x,
    ((strictSmoothExponents p q r x).filter
      fun z => (z.2.1, z.2.2) = e).card

/-- The explicit one-dimensional `p`-exponent fiber over a fixed `(q,r)`
pair. -/
def strictPExponentFiber (p q r x : ℕ) (e : ℕ × ℕ) : Finset ℕ :=
  (Finset.range x).filter fun i =>
    p ^ i * (q ^ e.1 * r ^ e.2) < x



/-- The literal restricted two-dimensional floor sum: sum the sizes of the
explicit `p`-exponent fibers over all admissible `(q,r)` pairs. -/
def restrictedFloorSum (p q r x : ℕ) : ℕ :=
  ∑ e ∈ strictSmoothPairs q r x,
    (strictPExponentFiber p q r x e).card

/-- Closed natural-log form of the restricted floor sum at the pure cutoff
`p^a`.  Every summand is the exact number of admissible `p`-exponents above
the fixed `(q,r)` pair. -/
def restrictedLogFloorSum (p q r a : ℕ) : ℕ :=
  ∑ e ∈ strictSmoothPairs q r (p ^ a),
    (a - Nat.log p (q ^ e.1 * r ^ e.2))

























/-! ## Generic logarithmic-window algebra -/

/-- Multiplicative base accumulated across a local window. -/
def windowBase (b : ℕ → ℤ) (lo : ℕ) : ℕ → ℤ
  | 0 => 1
  | len + 1 => b (lo + len) * windowBase b lo len

/-- Affine forcing accumulated across the same local window. -/
def windowForcing (b e : ℕ → ℤ) (lo : ℕ) : ℕ → ℤ
  | 0 => 0
  | len + 1 => b (lo + len) * windowForcing b e lo len + e (lo + len)















/-! ## Exact denominator-factor cancellation -/









/-- The exact remaining producer after local-window compression.  It is kept
as a named proposition, not asserted as a theorem. -/
def CofinalLocalWindowEscape
    (b m : ℕ → ℕ) (shortBound : ℕ → ℕ → ℕ) : Prop :=
  ∀ B : ℕ, 0 < B → Nat.Coprime B 30 →
    ∀ lo₀ : ℕ, ∃ lo len : ℕ,
      lo₀ ≤ lo ∧ 0 < len ∧
      0 < Int.natAbs (windowBase (fun n => b n) lo len) ∧
      shortBound B (lo + len) <
        leastPositiveResidue
          (Int.natAbs (windowBase (fun n => b n) lo len))
          (-((B : ℤ) *
            windowForcing (fun n => b n) (fun n => m n) lo len))



end ErdosProblems.Erdos269


