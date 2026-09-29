-- Prove2me | Definitions.Def_ErdosProblems_Erdos269_ThreePrimeRunningLcm
-- name    : ErdosProblems_Erdos269_ThreePrimeRunningLcm
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-27T18:11:42.611822+00:00
-- url     : https://prove2.me/theorems/a78abd0a-c269-4409-a2b4-137454af5f18
-- title:
--   ThreePrimeRunningLcm
-- statement:
--   Defines three-prime smooth values p^i q^j r^k, the product of the maximal pure prime powers below a cutoff, its reciprocal kernel, finite smooth prefixes and their LCM, height fibers, and dyadic block bases. The definitions alone do not claim irrationality.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L1-L912
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/269/erdos-269-three-prime-running-lcm.tex#L1-L260
--   Paper prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/269/erdos-269-three-prime-running-lcm.tex#L681-L689

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Erdős #269: the three-prime running-LCM coordinate

This module starts the problem-owned formalization of the first unresolved
three-prime case.  It records the exact computational height used by the
running-LCM representation, its cubic majorant, the smallest non-separation
fixture for `{2,3,5}`, the variable-base tail-state update, and the uniform
quadratic bound for actual filtered smooth-number shells.

No declaration here asserts irrationality or transcendence of a three-prime
value.  The missing producer is still an infinite residue-escape or genuinely
higher-dimensional analytic theorem.
-/

namespace ErdosProblems.Erdos269

open scoped BigOperators

/-- The `{p,q,r}`-smooth lattice point with exponent vector `(i,j,k)`. -/
def smooth3Val (p q r i j k : ℕ) : ℕ :=
  p ^ i * q ^ j * r ^ k

/-- The product of the largest pure `p`-, `q`-, and `r`-powers not exceeding
`x`.  For a `{p,q,r}`-smooth `x`, this is the running LCM of the smooth prefix. -/
def threePrimeHeight (p q r x : ℕ) : ℕ :=
  p ^ Nat.log p x * q ^ Nat.log q x * r ^ Nat.log r x

/-- The exact rational lattice kernel attached to the running-LCM height. -/
def threePrimeKernelQ (p q r i j k : ℕ) : ℚ :=
  (threePrimeHeight p q r (smooth3Val p q r i j k) : ℚ)⁻¹

/-- Exponent vectors of the actual `{p,q,r}`-smooth prefix up to `x`.  The
logarithmic box makes the prefix finite; the final filter keeps only products
which really lie below `x`. -/
def smoothPrefixExponents (p q r x : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((Finset.range (Nat.log p x + 1)).product
      ((Finset.range (Nat.log q x + 1)).product
        (Finset.range (Nat.log r x + 1)))).filter
    fun e => smooth3Val p q r e.1 e.2.1 e.2.2 ≤ x

/-- The literal running LCM of the finite smooth prefix. -/
def smoothPrefixLcm (p q r x : ℕ) : ℕ :=
  (smoothPrefixExponents p q r x).lcm
    fun e => smooth3Val p q r e.1 e.2.1 e.2.2





















/-! ## Finite pure-power jump enumeration -/

/-- The first `count` positive powers of one prime base.  Exponent zero is
omitted because it is the common initial value `1` in every channel. -/
def positivePrimePowers (p count : ℕ) : Finset ℕ :=
  (Finset.range count).image fun e => p ^ (e + 1)







/-- The finite union of the first `count` positive powers in each of the three
prime channels. -/
def threePrimePositiveJumpSet (p q r count : ℕ) : Finset ℕ :=
  (positivePrimePowers p count ∪ positivePrimePowers q count) ∪
    positivePrimePowers r count



/-- The finite jump set including the unique common origin `1`. -/
def threePrimeJumpSetWithOrigin (p q r count : ℕ) : Finset ℕ :=
  insert 1 (threePrimePositiveJumpSet p q r count)



/-! ## Single-coordinate jump ratios -/













/-! ## Finite jump grouping -/

/-- A finite rectangular exponent box.  This is the exact finite domain used
before passing to the infinite three-prime smooth series. -/
def smoothExponentBox (hp hq hr : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (Finset.range (hp + 1)).product
    ((Finset.range (hq + 1)).product (Finset.range (hr + 1)))

/-- The running-LCM height attached to one smooth exponent triple. -/
def smoothPointHeight (p q r : ℕ) (e : ℕ × ℕ × ℕ) : ℕ :=
  threePrimeHeight p q r (smooth3Val p q r e.1 e.2.1 e.2.2)

/-- The points of a finite exponent box with one fixed running-LCM height. -/
def smoothHeightFiber
    (p q r hp hq hr H : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (smoothExponentBox hp hq hr).filter fun e => smoothPointHeight p q r e = H







/-! The first exact `{2,3,5}` kernel values. -/















/-! ## Exact short-shell multiplicity bounds -/

/-- Exponent triples in a half-open multiplicative shell, with explicit
coordinate bounds.  The coordinate bounds are the interface to the pure-power
jump heights; the interval filter is the actual smooth-number shell. -/
def smoothExponentShell
    (p q r lo hi hp hq hr : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((Finset.range (hp + 1)).product
      ((Finset.range (hq + 1)).product (Finset.range (hr + 1)))).filter
    fun e => lo ≤ smooth3Val p q r e.1 e.2.1 e.2.2 ∧
      smooth3Val p q r e.1 e.2.1 e.2.2 < hi











/-! ## Exact dyadic block geometry for `{2,3,5}` -/

/-- A positive `p`-power lies strictly inside the dyadic block
`(2^a, 2^(a+1))`.  Endpoints are excluded because the dyadic jump itself is
the distinguished terminal factor of the compressed block. -/
def DyadicInternalPower (p a e : ℕ) : Prop :=
  2 ^ a < p ^ e ∧ p ^ e < 2 ^ (a + 1)









/-- The exact radix of the dyadic block after compressing all internal
`3`- and `5`-power jumps.  Each internal channel contributes its prime once,
and the terminal dyadic jump contributes the factor `2`. -/
noncomputable def dyadicBlockBase235 (a : ℕ) : ℕ :=
  by
    classical
    exact
      2 *
        (if ∃ e, DyadicInternalPower 3 a e then 3 else 1) *
        (if ∃ e, DyadicInternalPower 5 a e then 5 else 1)

















/-! ## Exact rank-two certificate -/



end ErdosProblems.Erdos269


