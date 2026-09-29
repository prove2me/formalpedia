-- Prove2me | solution 1 for SpectralFlatnessFactoring.covTop_pos
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T05:41:49.102983+00:00
-- url     : https://prove2.me/submissions/d3a52241-ac17-4b73-8a7f-ffdb7e9a228a

-- Sol generated from Novelty/SpectralFlatnessFactoring.lean
import Mathlib
import Definitions.Def_Novelty_SpectralFlatnessFactoring
import Definitions.Def_Novelty_WalshSpectralFlatness
import Theorems.Thm_SpectralFlatnessFactoring_hiSet_nonempty
import Theorems.Thm_SpectralFlatnessFactoring_testBit_top_iff
import Theorems.Thm_SpectralFlatnessFactoring_three_mul_le_of_testBit
import Theorems.Thm_SpectralFlatnessFactoring_topSet_ssubset
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

open SpectralFlatnessFactoring

open Finset SpectralFlatness

/-! ### The full odd support modulo `2^t` -/










/-! ### The zero-block theorem -/








/-! ### The top-bit law: the one structure that is not flat -/


/-- **The top-bit transmission law.**  For a balanced semiprime `N = p q` with
`2^{k-1} ≤ p ≤ q` (here `k = e + 2`), if the second-highest bit `p_{k-2}` of the smaller factor is
set then `N ≥ 2^{2k-1}`, i.e. the product carries out into its top bit.  This deterministic
implication is the entire source of the empirical `corr(p_{k-2}, N_{2k-1}) ≈ 0.285`. -/
theorem second_bit_transmits_to_top {e p q : ℕ} (hp : 2 ^ (e + 1) ≤ p) (hpq : p ≤ q)
    (hbit : p.testBit e = true) : 2 ^ (2 * e + 3) ≤ p * q := by
  have h3p : 3 * 2 ^ e ≤ p := three_mul_le_of_testBit hp hbit
  have h3q : 3 * 2 ^ e ≤ q := le_trans h3p hpq
  have hmul : (3 * 2 ^ e) * (3 * 2 ^ e) ≤ p * q := Nat.mul_le_mul h3p h3q
  have hpow : (3 * 2 ^ e) * (3 * 2 ^ e) = 9 * 2 ^ (2 * e) := by
    rw [two_mul, pow_add]; ring
  have h8 : 2 ^ (2 * e + 3) = 8 * 2 ^ (2 * e) := by rw [pow_add]; ring
  have : 8 * 2 ^ (2 * e) ≤ 9 * 2 ^ (2 * e) :=
    Nat.mul_le_mul_right _ (by norm_num)
  omega



/-- **Bit-level form of the transmission law.**  For a balanced semiprime with `k = e + 2` bit
factors, `p_{k-2} = 1` implies `N_{2k-1} = 1`: the second-highest bit of the hidden factor is
visible in the top bit of the public value. -/
theorem second_bit_transmits_to_top_bit {e p q : ℕ} (hp : 2 ^ (e + 1) ≤ p) (hpq : p ≤ q)
    (hq : q < 2 ^ (e + 2)) (hbit : p.testBit e = true) :
    (p * q).testBit (2 * e + 3) = true := by
  have hpq2 : p * q < 2 ^ (2 * e + 4) := by
    have hp2 : p < 2 ^ (e + 2) := lt_of_le_of_lt hpq hq
    calc p * q < 2 ^ (e + 2) * 2 ^ (e + 2) := by
          exact Nat.mul_lt_mul_of_lt_of_le hp2 (le_of_lt hq) (Nat.two_pow_pos (e + 2))
      _ = 2 ^ (2 * e + 4) := by rw [← pow_add]; ring_nf
  have := testBit_top_iff (N := p * q) (m := 2 * e + 3) (by simpa [Nat.add_assoc] using hpq2)
  exact this.mpr (second_bit_transmits_to_top hp hpq hbit)




/-! ### Cycle 2: the abstract mechanism, conditional balance, and a strictly positive top bias -/






/-! #### The top-bit bias is strictly positive at every size -/




theorem mem_balSupp {e : ℕ} {z : ℕ × ℕ} :
    z ∈ BalSupp e ↔ (z.1 < 2 ^ (e + 2) ∧ z.2 < 2 ^ (e + 2)) ∧ 2 ^ (e + 1) ≤ z.1 ∧ z.1 ≤ z.2 := by
  simp [BalSupp, Finset.mem_filter, Finset.mem_product, and_assoc]

/-- The transmission law as an inclusion of events. -/
theorem hiSet_subset_topSet (e : ℕ) : hiSet e ⊆ topSet e := by
  intro z hz
  rw [hiSet, Finset.mem_filter] at hz
  obtain ⟨hmem, hbit⟩ := hz
  rw [mem_balSupp] at hmem
  rw [topSet, Finset.mem_filter]
  exact ⟨mem_balSupp.mpr hmem,
    second_bit_transmits_to_top_bit hmem.2.1 hmem.2.2 hmem.1.2 hbit⟩





/-! ### Cycle 3: perfect secrecy of the low block -/









/-! ### Putting the two halves together -/



open SpectralFlatnessFactoring in
theorem solution(e : ℕ) : 0 < covTop e := by
  have hAB : hiSet e ∩ topSet e = hiSet e := Finset.inter_eq_left.mpr (hiSet_subset_topSet e)
  have hApos : 0 < (hiSet e).card := Finset.card_pos.mpr (hiSet_nonempty e)
  have hBlt : (topSet e).card < (BalSupp e).card := Finset.card_lt_card (topSet_ssubset e)
  have hSpos : 0 < (BalSupp e).card := lt_of_le_of_lt (Nat.zero_le _) hBlt
  have hS : (0 : ℚ) < ((BalSupp e).card : ℚ) := by exact_mod_cast hSpos
  have hA : (0 : ℚ) < ((hiSet e).card : ℚ) := by exact_mod_cast hApos
  have hB : ((topSet e).card : ℚ) < ((BalSupp e).card : ℚ) := by exact_mod_cast hBlt
  rw [covTop, hAB]
  have key : ((hiSet e).card : ℚ) / ((BalSupp e).card : ℚ)
      - ((hiSet e).card : ℚ) / ((BalSupp e).card : ℚ)
        * (((topSet e).card : ℚ) / ((BalSupp e).card : ℚ))
      = (((hiSet e).card : ℚ) / ((BalSupp e).card : ℚ))
        * ((((BalSupp e).card : ℚ) - ((topSet e).card : ℚ)) / ((BalSupp e).card : ℚ)) := by
    field_simp
  rw [key]
  apply mul_pos (div_pos hA hS)
  exact div_pos (by linarith) hS
