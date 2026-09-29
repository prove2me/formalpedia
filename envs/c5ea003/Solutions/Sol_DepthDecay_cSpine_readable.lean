-- Prove2me | solution 1 for DepthDecay.cSpine_readable
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T05:24:31.724903+00:00
-- url     : https://prove2.me/submissions/f119066b-05ff-4172-9056-45924f562f03

-- Sol generated from Cryptography/DepthDecay/NullBeyondInversion.lean
import Mathlib
import Definitions.Def_Cryptography_DepthDecay_NullBeyondInversion
import Definitions.Def_Cryptography_DepthDecay_WindowSensor
import Theorems.Thm_DepthDecay_cRun_letters_C
import Theorems.Thm_DepthDecay_letterAt_eq_of_probe_one_of_prefix_C

/-!
# The magnitude channel is null beyond the first inversion

`Cryptography.DepthDecay.WindowSensor` shows that a one-bit magnitude probe of an
admissible pair `(m,n)` already determines the whole leading `C`-run of the
Berggren descent *and* the inversion letter that terminates it.  Here we prove
the matching negative statement, which is the formal content of the observed
depth decay of the magnitude channel:

> **No fixed window budget `W` determines the letter that follows the first
> inversion, at any prescribed depth.**

For every window budget `W`, every depth `k` and every admissible scale `q` we
construct two admissible pairs `sP q k` and `sM q k` whose `2^W`-window probes are
*equal*, whose descent paths agree on the whole prefix of length `k+1` (namely
`C^k B`), and which nevertheless differ at depth `k+1`.

The construction is the two sides of the non-dyadic branch boundary `r = 7/3` of
the second Gauss digit:

* `sP q k = ((7+6k)q + 1, 3q)`, ratio `7/3 + 2k + 1/(3q)`,
* `sM q k = ((7+6k)q - 1, 3q)`, ratio `7/3 + 2k - 1/(3q)`.

As soon as `2^W < q` both ratios lie in the same dyadic interval of width `2^{-W}`
— the sensor cannot separate them — yet after the `k` translations `r ↦ r-2` and
the inversion `r ↦ 1/(r-2)` the images straddle the cut point `3`, and the next
letters are `B` and `C` respectively.  The information the sensor would need is
the *fine* Gauss digit of the ratio, which no fixed-precision window supplies.

Because `q` is free, the counterexamples occur at arbitrarily large denominators:
see `depth_null_unbounded`.
-/

open DepthDecay

/-! ### The straddling pair -/
















/-! ### Admissibility of the straddling pair -/







/-! ### The window sensor cannot separate the pair -/


/-! ### The common prefix `C^k B` -/







/-! ### Divergence one step later -/


/-! ### Main theorems -/





/-! ### Sharp threshold, and the surviving `C`-spine -/




open DepthDecay in
theorem solution(L : ℕ) :
    Adm (2 * L + 2, 1) ∧ (∀ j < L, letterAt j (2 * L + 2, 1) = Letter.C) ∧
      (∀ s' : ℕ × ℕ, Adm s' → probe 1 (2 * L + 2, 1) = probe 1 s' →
        ∀ j ≤ L, letterAt j (2 * L + 2, 1) = letterAt j s') := by
  have hAdm : Adm (2 * L + 2, 1) := by
    refine ⟨by norm_num, ?_, ?_, ?_⟩
    · show (1 : ℕ) < 2 * L + 2
      omega
    · show Nat.gcd (2 * L + 2) 1 = 1
      simp
    · show (2 * L + 2 + 1) % 2 = 1
      omega
  have hrun : ∀ j < L, letterAt j (2 * L + 2, 1) = Letter.C := by
    intro j hj
    exact cRun_letters_C hAdm j (by show j < ((2 * L + 2 : ℕ) - 1) / (2 * 1); omega)
  refine ⟨hAdm, hrun, ?_⟩
  intro s' h' hp j hj
  exact letterAt_eq_of_probe_one_of_prefix_C j hAdm h' hp
    (fun i hi => hrun i (lt_of_lt_of_le hi hj))
