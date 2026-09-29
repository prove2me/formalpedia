-- Prove2me | solution 1 for SpectralFlatnessFactoring.fiber_sum_bitSign_zero
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T05:43:58.891383+00:00
-- url     : https://prove2.me/submissions/f8b2cbca-3ae1-4618-b116-f9ab172f131e

-- Sol generated from Novelty/SpectralFlatnessFactoring.lean
import Mathlib
import Definitions.Def_Novelty_SpectralFlatnessFactoring
import Definitions.Def_Novelty_WalshSpectralFlatness
import Theorems.Thm_SpectralFlatnessFactoring_oddRes_mul_injOn
import Theorems.Thm_SpectralFlatnessFactoring_sum_bitSign_oddRes
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


theorem mem_oddRes {t x : ℕ} : x ∈ OddRes t ↔ x < 2 ^ t ∧ x % 2 = 1 := by simp [OddRes]





theorem oddRes_mul_mem {t p q : ℕ} (ht : 1 ≤ t) (hp : p ∈ OddRes t) (hq : q ∈ OddRes t) :
    p * q % 2 ^ t ∈ OddRes t := by
  rw [mem_oddRes] at hp hq ⊢
  refine ⟨Nat.mod_lt _ (Nat.two_pow_pos t), ?_⟩
  have hd : (2 : ℕ) ∣ 2 ^ t := dvd_pow_self 2 (by omega)
  rw [Nat.mod_mod_of_dvd _ hd]
  have h := Nat.mul_mod p q 2
  rw [hp.2, hq.2] at h
  simpa using h


/-- **Simple transitivity.**  Multiplication by a fixed odd residue permutes the odd residues:
the public value `N = p q mod 2^t` is a bijective reparametrisation of the cofactor `q`. -/
theorem oddRes_mul_image {t p : ℕ} (ht : 1 ≤ t) (hp : p ∈ OddRes t) :
    (OddRes t).image (fun q => p * q % 2 ^ t) = OddRes t := by
  have hinj : Set.InjOn (fun q => p * q % 2 ^ t) (OddRes t) := oddRes_mul_injOn hp
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro y hy
    simp only [mem_image] at hy
    obtain ⟨q, hq, rfl⟩ := hy
    exact oddRes_mul_mem ht hp hq
  · rw [Finset.card_image_of_injOn hinj]

/-! ### The zero-block theorem -/








/-! ### The top-bit law: the one structure that is not flat -/









/-! ### Cycle 2: the abstract mechanism, conditional balance, and a strictly positive top bias -/






/-! #### The top-bit bias is strictly positive at every size -/










/-! ### Cycle 3: perfect secrecy of the low block -/









/-! ### Putting the two halves together -/



open SpectralFlatnessFactoring in
theorem solution{t j N : ℕ} (hj : 1 ≤ j) (hjt : j < t) (hN : N ∈ OddRes t) :
    ∑ z ∈ fiber t N, bitSign j z.1 = 0 := by
  have ht : 1 ≤ t := by omega
  have hbij : ∑ z ∈ fiber t N, bitSign j z.1 = ∑ p ∈ OddRes t, bitSign j p := by
    refine Finset.sum_bij (fun z _ => z.1) ?_ ?_ ?_ ?_
    · intro z hz
      simp only [fiber, Finset.mem_filter, Finset.mem_product] at hz
      exact hz.1.1
    · intro z hz w hw hzw
      simp only [fiber, Finset.mem_filter, Finset.mem_product] at hz hw
      have hzw' : z.1 = w.1 := hzw
      have h1 : z.1 * z.2 % 2 ^ t = w.1 * w.2 % 2 ^ t := by rw [hz.2, hw.2]
      rw [hzw'] at h1
      have h2 : z.2 = w.2 :=
        oddRes_mul_injOn hw.1.1 (by simpa using hz.1.2) (by simpa using hw.1.2) h1
      exact Prod.ext hzw' h2
    · intro p hp
      have himg : N ∈ (OddRes t).image (fun q => p * q % 2 ^ t) := by
        rw [oddRes_mul_image ht hp]; exact hN
      rw [Finset.mem_image] at himg
      obtain ⟨q, hq, hqe⟩ := himg
      refine ⟨(p, q), ?_, rfl⟩
      simp only [fiber, Finset.mem_filter, Finset.mem_product]
      exact ⟨⟨hp, hq⟩, hqe⟩
    · intro z _; rfl
  rw [hbij, sum_bitSign_oddRes hj hjt]
