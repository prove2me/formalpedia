-- Prove2me | solution 1 for EulerTwoSquares.euler_scan_quartic_bound
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-17T19:29:37.860633+00:00
-- url     : https://prove2.me/submissions/ff28a6c5-e484-4907-a4ba-f29f22bef708

-- Sol generated from Algebra/EulerTwoSquaresBarrier.lean
import Mathlib
import Theorems.Thm_EulerTwoSquares_quartic_barrier_sorted

/-!
# An unconditional quartic barrier for representation search

Euler's method has to *find* two essentially distinct representations `N = a²+b² = c²+d²`.
The natural search walks the smaller part upward, `1, 2, 3, …`, testing whether `N - a²` is a
square.  How far must such a walk go before it has seen **both** representations?

This file answers that with an exact, unconditional inequality.  Write the two
representations in sorted form `a ≤ b`, `c ≤ d`.  If they are different then their large
parts differ, say `d < b`, hence `b ≥ d + 1` and therefore

`c² = b² - d² + a² ≥ 2d + 1`,   while   `2N = 2c² + 2d² ≤ 4d² < (2d+1)²`,

so `2N < c⁴`.  In other words **the larger of the two small parts exceeds `(2N)^{1/4}`**
(`EulerTwoSquares.quartic_barrier`, `EulerTwoSquares.euler_scan_quartic_bound`).  No primality,
no genericity, no averaging: two distinct representations simply cannot both be "shallow".

Combined with `EulerTwoSquares.fermat_halts_immediately_iff` this gives the sharpest form of
the cost comparison (`EulerTwoSquares.euler_loses_on_balanced`): on a balanced eligible
semiprime — where Fermat's difference-of-squares scan succeeds on its *first* trial — any
representation search that collects both representations must reach a bound `t` with
`t⁴ > 2N`, i.e. `t > (2N)^{1/4}`.  The measured constant-factor loss of the representation
route is therefore not an artefact of the sampling distribution on the balanced side: it is
forced.
-/

open EulerTwoSquares

/-! ## The barrier -/






/-! ## EULER-LOSES on balanced instances -/

variable {p q : ℕ}




open EulerTwoSquares in
theorem solution{N a b c d t : ℤ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) (h1 : a ^ 2 + b ^ 2 = N) (h2 : c ^ 2 + d ^ 2 = N)
    (hne1 : ¬(c = a ∧ d = b)) (hne2 : ¬(d = a ∧ c = b))
    (hta : min a b ≤ t) (htc : min c d ≤ t) : 2 * N < t ^ 4 := by
  have hkey : 2 * N < max (min a b) (min c d) ^ 4 := by
    have h2' : b ^ 2 + a ^ 2 = N := by linarith
    have h2'' : d ^ 2 + c ^ 2 = N := by linarith
    rcases le_total a b with hx | hx <;> rcases le_total c d with hy | hy
    · rw [min_eq_left hx, min_eq_left hy]
      exact quartic_barrier_sorted ha.le hx hc.le hy h1 h2
        (fun hh => hne1 ⟨hh.1.symm, hh.2.symm⟩)
    · rw [min_eq_left hx, min_eq_right hy]
      exact quartic_barrier_sorted ha.le hx hd.le hy h1 h2''
        (fun hh => hne2 ⟨hh.1.symm, hh.2.symm⟩)
    · rw [min_eq_right hx, min_eq_left hy]
      exact quartic_barrier_sorted hb.le hx hc.le hy h2' h2
        (fun hh => hne2 ⟨hh.2.symm, hh.1.symm⟩)
    · rw [min_eq_right hx, min_eq_right hy]
      exact quartic_barrier_sorted hb.le hx hd.le hy h2' h2''
        (fun hh => hne1 ⟨hh.2.symm, hh.1.symm⟩)
  have hmax : max (min a b) (min c d) ≤ t := max_le hta htc
  have hmax0 : (0 : ℤ) ≤ max (min a b) (min c d) :=
    le_max_of_le_left (le_min ha.le hb.le)
  have : max (min a b) (min c d) ^ 4 ≤ t ^ 4 := pow_le_pow_left₀ hmax0 hmax 4
  linarith
