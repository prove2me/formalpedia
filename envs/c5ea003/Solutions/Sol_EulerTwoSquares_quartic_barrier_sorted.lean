-- Prove2me | solution 1 for EulerTwoSquares.quartic_barrier_sorted
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-17T19:27:56.053439+00:00
-- url     : https://prove2.me/submissions/b7933a1b-c1f5-4bf0-985f-fc27f5a25a7d

-- Sol generated from Algebra/EulerTwoSquaresBarrier.lean
import Mathlib
import Theorems.Thm_EulerTwoSquares_quartic_barrier_gap

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


/-- **Quartic barrier, sorted form.**  Two representations of the same `N` in sorted form whose
larger parts satisfy `d < b` force `2N < c⁴`, where `c` is the small part of the *second*
representation. -/
theorem quartic_barrier {N a b c d : ℤ} (ha : 0 ≤ a) (hab : a ≤ b) (hc : 0 ≤ c) (hcd : c ≤ d)
    (h1 : a ^ 2 + b ^ 2 = N) (h2 : c ^ 2 + d ^ 2 = N) (hlt : d < b) : 2 * N < c ^ 4 := by
  have := quartic_barrier_gap (k := 1) ha hab hc hcd h1 h2 one_pos (by linarith)
  linarith [this]




/-! ## EULER-LOSES on balanced instances -/

variable {p q : ℕ}




open EulerTwoSquares in
theorem solution{N a b c d : ℤ} (ha : 0 ≤ a) (hab : a ≤ b) (hc : 0 ≤ c)
    (hcd : c ≤ d) (h1 : a ^ 2 + b ^ 2 = N) (h2 : c ^ 2 + d ^ 2 = N) (hne : ¬(a = c ∧ b = d)) :
    2 * N < max a c ^ 4 := by
  have hbd : b ≠ d := by
    intro hbd
    refine hne ⟨?_, hbd⟩
    have hac : a ^ 2 = c ^ 2 := by rw [hbd] at h1; linarith
    nlinarith
  rcases lt_trichotomy d b with hlt | heq | hlt
  · have h := quartic_barrier ha hab hc hcd h1 h2 hlt
    have hle : c ^ 4 ≤ max a c ^ 4 := by
      have : c ≤ max a c := le_max_right _ _
      exact pow_le_pow_left₀ hc this 4
    linarith
  · exact absurd heq.symm hbd
  · have h := quartic_barrier hc hcd ha hab h2 h1 hlt
    have hle : a ^ 4 ≤ max a c ^ 4 := by
      have : a ≤ max a c := le_max_left _ _
      exact pow_le_pow_left₀ ha this 4
    linarith
