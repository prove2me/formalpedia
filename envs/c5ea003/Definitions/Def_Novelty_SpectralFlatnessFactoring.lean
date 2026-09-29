-- Prove2me | Definitions.Def_Novelty_SpectralFlatnessFactoring
-- name    : Novelty_SpectralFlatnessFactoring
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:42:09.645331+00:00
-- url     : https://prove2.me/theorems/53d4e7f3-0b6e-44da-b3d8-8d7fc84387c1
-- title:
--   Aether Catalog definitions — Novelty_SpectralFlatnessFactoring
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.SpectralFlatnessFactoring`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/SpectralFlatnessFactoring.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Novelty_WalshSpectralFlatness
/-
# The spectral face of the factoring barrier: an exact zero-block theorem and the top-bit law

Companion to `Novelty.WalshSpectralFlatness`.  Where that file develops the Walsh calculus on the
Boolean cube, this file proves the two *arithmetic* facts that the spectral experiment
(Paper 53, Experiment 388) measured numerically:

1. **Zero block (flatness, exact).**  Let `t ≥ 2` and let the support be the full odd support
   modulo `2^t`: all ordered pairs `(p,q)` of odd residues, with public value `N = p q mod 2^t`.
   Then for every bit index `1 ≤ j < t` and **every** predictor `h` — arbitrary, not merely a
   low-degree GF(2) parity — the bit `p_j` of the secret factor is right exactly half the time.
   The correlation is *exactly* `0`, not `O(m^{-1/2})`.
   (`SpectralFlatnessFactoring.lowblock_corr_zero`,
    `SpectralFlatnessFactoring.lowblock_predictor_barrier`.)

2. **Top bit (the only non-flat structure).**  For a balanced semiprime `N = p q` with
   `2^{k-1} ≤ p ≤ q < 2^k`, the second-highest bit of the smaller factor is *transmitted* to the
   top bit of `N`: `p_{k-2} = 1 ⟹ N_{2k-1} = 1`, equivalently `N < 2^{2k-1} ⟹ p_{k-2} = 0`.
   This deterministic one-sided law is the source of the empirically observed
   `corr(p_{k-2}, N_{2k-1}) ≈ 0.285`, and it is a pure magnitude statement: the predicate
   `N ≥ 2^{2k-1}` is symmetric in `(p,q)` and is computable from `N` alone.
   (`SpectralFlatnessFactoring.second_bit_transmits_to_top`,
    `SpectralFlatnessFactoring.second_bit_zero_of_top_bit_zero`.)
   It is genuinely one-sided: `top_bit_does_not_determine_second_bit` exhibits two balanced
   semiprimes with the same top bit and different `p_{k-2}`, and
   `top_bit_does_not_determine_low_bit` does the same for a low bit.

3. **Perfect secrecy of the low block.**  Strengthening (1): conditioned on any public value,
   the secret factor is *equidistributed* over the whole unit group, so any two public values
   induce identical distributions on any property of the secret factor at all
   (`fiber_distribution_independent`), every fiber has exactly `2^{t-1}` points
   (`fiber_card`), and no guessing strategy hits more than one of them (`guess_card_le_one`).
   The mechanism is isolated abstractly in `group_zero_block`: it is the simple transitivity of
   the regular representation, not anything about primes.

4. **The top-bit bias is strictly positive at every size** (`covTop_pos`): over the full balanced
   integer support the covariance of `p_{k-2} = 1` with `N_{2k-1} = 1` is `> 0` for every `k`,
   so the contrast between the exactly-flat low block and the non-flat top-bit family is a
   theorem, not a numerical impression.

The results together are the formal content of the experiment's verdict: *all* the structure
that the Walsh spectrum sees is the symmetric magnitude/carry family of the top bits, and on the
low block the spectrum is exactly, provably flat.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): the observed decay `corr(f_3,{1,2,3}) = 0.203 → 0.013` and
`corr(p_2, N_{2k-1}) = 0.254/0.166/0.013/0.006` at `k = 8/10/12/14` is not a slow asymptotic
approach to a nonzero limit but a finite-sample fluctuation around an *exactly zero* population
value.  If so, there must be an exact cancellation on the unrestricted (odd) support.

Experiment (Experimenter): a direct enumeration over the full odd support mod `2^t` for
`t = 4,5,6` (see `ComputationalEvidence.md`) gives, for every `1 ≤ j < t` and every parity of the
low block, correlation exactly `0` in exact rational arithmetic — not `10^{-3}`.  Per public value
the counts are exactly `(8,8)` for all 16 fibers at `t = 5` and `(16,16)` for all 32 fibers at
`t = 6`.  Restricting the support to `p < q` (the "smaller factor" convention) reintroduces
correlations at the `m^{-1/2}` scale (`2/15, 2/31, 1/21` at `t = 5,6,7`), and restricting further
to primes reproduces the reported `0.254 / 0.166` at `k = 8 / 10` for the `j = 2` anomaly, with
sign flips at `k = 7, 9` identifying it as a fluctuation.

Analysis (Analyst): the mechanism is the simply transitive action of the odd residues on
themselves.  For a *fixed* multiplier `p`, the map `q ↦ p q mod 2^t` permutes the odd residues, so
the public value `N` is independent of `p` in the exact, distributional sense; the sign
`(-1)^{p_j}` then factors out of the double sum and vanishes because `x ↦ x XOR 2^j` is a
sign-reversing involution of the odd residues.  Both ingredients are exact; neither survives the
restriction to `p < q`, which is precisely the reported source of the residual `m^{-1/2}` noise.

Critique (Critic): the theorem is about the odd support, not the prime support, and about ordered
pairs, not the `min`.  Both restrictions are recorded honestly here: the involution `x ↦ x XOR 2^j`
does not preserve `p < q`, so the exact statement provably does not transfer to the ordered
support — which is exactly why the experiment sees `O(m^{-1/2})` and not `0` there.  The top-bit
law, by contrast, is unconditional and holds for every balanced semiprime.
-/

namespace SpectralFlatnessFactoring

open Finset SpectralFlatness

/-! ### The full odd support modulo `2^t` -/

/-- The odd residues mod `2^t`: the "full odd support" of the experiment. -/
def OddRes (t : ℕ) : Finset ℕ := (Finset.range (2 ^ t)).filter fun x => x % 2 = 1


/-- `±1` encoding of bit `j`. -/
noncomputable def bitSign (j x : ℕ) : ℝ := sgn (x.testBit j)







/-! ### The zero-block theorem -/


/-- The Walsh character (GF(2) parity) of a set `S` of bit positions of a natural number. -/
noncomputable def natParity (S : Finset ℕ) (N : ℕ) : ℝ := ∏ i ∈ S, sgn (N.testBit i)






/-! ### The top-bit law: the one structure that is not flat -/









/-! ### Cycle 2: the abstract mechanism, conditional balance, and a strictly positive top bias -/


/-- The fiber of the public value: all factorisations of `N` in the odd support mod `2^t`. -/
def fiber (t N : ℕ) : Finset (ℕ × ℕ) :=
  (OddRes t ×ˢ OddRes t).filter fun z => z.1 * z.2 % 2 ^ t = N




/-! #### The top-bit bias is strictly positive at every size -/

/-- The balanced support at half-size `k = e + 2`: all ordered pairs `2^{k-1} ≤ p ≤ q < 2^k`. -/
def BalSupp (e : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (2 ^ (e + 2))) ×ˢ (Finset.range (2 ^ (e + 2)))).filter
    fun z => 2 ^ (e + 1) ≤ z.1 ∧ z.1 ≤ z.2

/-- Pairs whose smaller factor has its second-highest bit set. -/
def hiSet (e : ℕ) : Finset (ℕ × ℕ) := (BalSupp e).filter fun z => z.1.testBit e = true

/-- Pairs whose product carries out into the top bit. -/
def topSet (e : ℕ) : Finset (ℕ × ℕ) :=
  (BalSupp e).filter fun z => (z.1 * z.2).testBit (2 * e + 3) = true





/-- The covariance of the two indicator events `p_{k-2} = 1` and `N_{2k-1} = 1` over the balanced
support. -/
def covTop (e : ℕ) : ℚ :=
  (((hiSet e ∩ topSet e).card : ℚ) / ((BalSupp e).card : ℚ))
    - (((hiSet e).card : ℚ) / ((BalSupp e).card : ℚ))
      * (((topSet e).card : ℚ) / ((BalSupp e).card : ℚ))


/-! ### Cycle 3: perfect secrecy of the low block -/









/-! ### Putting the two halves together -/


end SpectralFlatnessFactoring


