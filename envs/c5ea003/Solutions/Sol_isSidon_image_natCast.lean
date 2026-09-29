-- Prove2me | solution 1 for isSidon_image_natCast
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T02:13:21.280152+00:00
-- url     : https://prove2.me/submissions/ddbc361d-77f4-4729-ab07-ca1c05f8f90a

-- Sol generated from Shared/SidonSetsCyclic.lean
import Mathlib
import Definitions.Def_Shared_SidonSetsCyclic
import Definitions.Def_Shared_SidonSetsErdosTuran

/-!
# Sidon sets III: the cyclic Erdős–Turán sandwich

Third cycle of the Sidon-set research thread.  Cycle 1 built the Erdős–Turán set in
`ℕ` and the sandwich `√(N/8) < maxSidonCard N ≤ √(2N) + 1`; cycle 2 established the
counting characterisation, extremal rigidity, and a Reiman double count.  Here we lift
the whole theory from the *interval* `{0, …, N-1}` to the *cyclic group* `ZMod N`, where
wrap-around could a priori destroy the uniqueness of representations.

## Main results

* `ErdosTuran.shift_absurd` — the shifted digit identity `k₃ + k₄ = k₁ + k₂ + p` is
  incompatible with the Erdős–Turán quadratic-residue identity; this is the extra input
  needed beyond cycle 1.
* `ErdosTuran.etSet_isSidon_mod` — **the Erdős–Turán set is Sidon modulo `2p²`**, a
  strictly stronger statement than `etSet_isSidon`: the sums live in `[0, 4p²)`, so a
  congruence modulo `2p²` is either a genuine equality (handled by cycle 1) or a shift
  by exactly `2p²` (excluded by `shift_absurd`).
* `ErdosTuran.etSetZMod_isSidon`, `ErdosTuran.etSetZMod_card` — hence `ZMod (2p²)`
  contains a Sidon set of size `p`.
* `ErdosTuran.zmod_sidon_sandwich_prime` — in `ZMod (2p²)`, of order `N = 2p²`, the
  largest Sidon set has size between `√(N/2)` and `√N + 1`: a factor `√2`.
* `isSidon_image_natCast` — **transfer principle**: a Sidon subset of `{0, …, n-1}`
  remains Sidon in `ZMod N` for every `N ≥ 2n`.
* `zmod_sidon_sandwich` — **for every `N ≥ 64`**, the largest Sidon set in `ZMod N` has
  size strictly between `√(N/16)` and `√N + 1`; so `ZMod N` also realises `Θ(√N)`.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): Cycle 2 showed the Sidon property is a single injectivity.
  The bold question for cycle 3: does that injectivity survive *quotienting*?  Three
  conjectures were tabled.
  (S1) The Erdős–Turán set is Sidon not just in `ℤ` but already in `ℤ/2p²ℤ` — the
       tightest cyclic modulus for which its elements are distinct.
  (S2) Sidon-ness in `ℤ/Nℤ` is *not* automatic from Sidon-ness in an interval; a
       modulus barely larger than the diameter should fail.
  (S3) Every cyclic group of order `N` contains a Sidon set of size `Θ(√N)`.
Experiment (Experimenter): (S1) was proved.  Direct evaluation first *found* the
  phenomenon: `etSet p` is Sidon mod `2p²` for `p = 3, 5, 7, 11, 13`, but Sidon mod
  `2p² + 1` fails for all of them, so (S2) holds computationally and (S1) is sharp in
  the modulus.  The formal proof isolates the only obstruction: two sums of pairs both
  lie in `[0, 4p²)`, so their difference is `0` or `±2p²`; the shifted case forces
  `k₃ + k₄ = k₁ + k₂ + p`, which `shift_absurd` refutes because `etKey` already forces
  `k₃ + k₄ = k₁ + k₂` exactly.  (S3) was proved via a transfer principle plus
  Bertrand's postulate.
Analysis (Analyst): The reason wrap-around is harmless at modulus exactly `2p²` is
  arithmetic, not accidental: `2p² = 2p · p`, so a shift by the modulus is a shift of
  the *high* `2p`-adic digit by exactly `p`, and the Vieta rigidity of cycle 1 pins the
  high digit sum on the nose.  At modulus `2p² + 1` the shift is no longer a clean digit
  shift, and the construction breaks — exactly as observed numerically.
Critique (Critic): `etSet_isSidon_mod` is not vacuous: `etSetZMod p` has `p` distinct
  elements (`etSetZMod_card`), so there are genuinely `C(p+1,2)` distinct pairwise sums
  being separated.  The general result `zmod_sidon_sandwich` is guarded by `N ≥ 64`,
  needed so that `Nat.sqrt (N / 16) ≥ 2` and Bertrand's window contains an odd prime;
  the bound is not claimed below that.  No step uses `decide` or `native_decide`.
Synthesis (PI): the additive-combinatorial rigidity of cycle 1 is strong enough to
  survive the quotient by `2p²`; the interval theory and the cyclic theory therefore
  agree to within an absolute constant, and both are `Θ(√N)`.
-/

open Finset


open ErdosTuran

variable {p : ℕ}




open ErdosTuran

variable {p : ℕ}







/-! ## Transfer of Sidon sets from `ℕ` to arbitrary cyclic groups -/





theorem solution{A : Finset ℕ} {n N : ℕ} (hA : IsSidon A)
    (hsub : A ⊆ Finset.range n) (hN : 2 * n ≤ N) :
    IsSidon (A.image (fun a : ℕ => (a : ZMod N))) := by
  intro a ha b hb c hc d hd hsum
  simp only [Finset.mem_image] at ha hb hc hd
  obtain ⟨u, hu, rfl⟩ := ha
  obtain ⟨v, hv, rfl⟩ := hb
  obtain ⟨w, hw, rfl⟩ := hc
  obtain ⟨x, hx, rfl⟩ := hd
  have hu' : u < n := Finset.mem_range.mp (hsub hu)
  have hv' : v < n := Finset.mem_range.mp (hsub hv)
  have hw' : w < n := Finset.mem_range.mp (hsub hw)
  have hx' : x < n := Finset.mem_range.mp (hsub hx)
  have hcast : ((u + v : ℕ) : ZMod N) = ((w + x : ℕ) : ZMod N) := by push_cast; exact hsum
  have hmod : (u + v) % N = (w + x) % N := (ZMod.natCast_eq_natCast_iff' _ _ _).mp hcast
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hmod
  rcases hA u hu v hv w hw x hx hmod with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨by rw [h1], by rw [h2]⟩
  · exact Or.inr ⟨by rw [h1], by rw [h2]⟩
