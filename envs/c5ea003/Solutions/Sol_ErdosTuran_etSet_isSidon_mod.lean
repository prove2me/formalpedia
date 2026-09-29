-- Prove2me | solution 1 for ErdosTuran.etSet_isSidon_mod
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T22:55:19.51993+00:00
-- url     : https://prove2.me/submissions/84f85711-37ac-4872-905b-cd4b394fa233

-- Sol generated from Shared/SidonSetsCyclic.lean
import Mathlib
import Definitions.Def_Shared_SidonSetsCyclic
import Definitions.Def_Shared_SidonSetsErdosTuran
import Theorems.Thm_ErdosTuran_etKey
import Theorems.Thm_ErdosTuran_etMap_add
import Theorems.Thm_ErdosTuran_etMap_lt
import Theorems.Thm_ErdosTuran_etSet_isSidon
import Theorems.Thm_ErdosTuran_mem_etSet_iff
import Theorems.Thm_base_digits_unique

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

/-- A shifted digit identity is impossible: `etKey` forces `k₁ + k₂ = k₃ + k₄`, which
contradicts a shift by `p`. -/
theorem shift_absurd (hp : p.Prime) (hodd : p ≠ 2) {k₁ k₂ k₃ k₄ : ℕ}
    (h₁ : k₁ < p) (h₂ : k₂ < p) (h₃ : k₃ < p) (h₄ : k₄ < p)
    (hS : k₃ + k₄ = k₁ + k₂ + p)
    (hr : k₁ ^ 2 % p + k₂ ^ 2 % p = k₃ ^ 2 % p + k₄ ^ 2 % p) : False := by
  have hsZ : ((k₁ : ZMod p)) + (k₂ : ZMod p) = (k₃ : ZMod p) + (k₄ : ZMod p) := by
    have h := congrArg (fun n : ℕ => (n : ZMod p)) hS
    push_cast at h
    rw [ZMod.natCast_self] at h
    rw [h]; ring
  rcases etKey hp hodd h₁ h₂ h₃ h₄ hsZ hr with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;>
    · subst e1; subst e2; omega



open ErdosTuran

variable {p : ℕ}







/-! ## Transfer of Sidon sets from `ℕ` to arbitrary cyclic groups -/





open ErdosTuran in
theorem solution(hp : p.Prime) (hodd : p ≠ 2) :
    ∀ u ∈ etSet p, ∀ v ∈ etSet p, ∀ w ∈ etSet p, ∀ x ∈ etSet p,
      (u + v) % (2 * p ^ 2) = (w + x) % (2 * p ^ 2) →
      (u = w ∧ v = x) ∨ (u = x ∧ v = w) := by
  have hp0 : 0 < p := hp.pos
  have hM : 0 < 2 * p ^ 2 := by positivity
  intro u hu v hv w hw x hx hcong
  obtain ⟨k₁, hk₁, rfl⟩ := mem_etSet_iff.mp hu
  obtain ⟨k₂, hk₂, rfl⟩ := mem_etSet_iff.mp hv
  obtain ⟨k₃, hk₃, rfl⟩ := mem_etSet_iff.mp hw
  obtain ⟨k₄, hk₄, rfl⟩ := mem_etSet_iff.mp hx
  have hmod : ∀ k : ℕ, k ^ 2 % p < p := fun k => Nat.mod_lt _ hp0
  -- the two sums, in `2p`-adic digit form
  have hA : etMap p k₁ + etMap p k₂ = 2 * p * (k₁ + k₂) + (k₁ ^ 2 % p + k₂ ^ 2 % p) :=
    etMap_add k₁ k₂
  have hB : etMap p k₃ + etMap p k₄ = 2 * p * (k₃ + k₄) + (k₃ ^ 2 % p + k₄ ^ 2 % p) :=
    etMap_add k₃ k₄
  -- both sums are `< 4p²`
  have hAlt : etMap p k₁ + etMap p k₂ < 4 * p ^ 2 := by
    have := etMap_lt hp0 hk₁; have := etMap_lt hp0 hk₂; omega
  have hBlt : etMap p k₃ + etMap p k₄ < 4 * p ^ 2 := by
    have := etMap_lt hp0 hk₃; have := etMap_lt hp0 hk₄; omega
  -- a congruence between two numbers `< 2M` is an equality or a shift by `M`
  have hme : (etMap p k₁ + etMap p k₂) ≡ (etMap p k₃ + etMap p k₄) [MOD 2 * p ^ 2] := hcong
  obtain ⟨c, hc⟩ := Nat.ModEq.dvd hme
  have hX2 : etMap p k₁ + etMap p k₂ < 2 * (2 * p ^ 2) := by linarith
  have hY2 : etMap p k₃ + etMap p k₄ < 2 * (2 * p ^ 2) := by linarith
  have hXz : ((etMap p k₁ + etMap p k₂ : ℕ) : ℤ) < 2 * ((2 * p ^ 2 : ℕ) : ℤ) := by
    exact_mod_cast hX2
  have hYz : ((etMap p k₃ + etMap p k₄ : ℕ) : ℤ) < 2 * ((2 * p ^ 2 : ℕ) : ℤ) := by
    exact_mod_cast hY2
  have hXz0 : (0 : ℤ) ≤ ((etMap p k₁ + etMap p k₂ : ℕ) : ℤ) := Int.natCast_nonneg _
  have hYz0 : (0 : ℤ) ≤ ((etMap p k₃ + etMap p k₄ : ℕ) : ℤ) := Int.natCast_nonneg _
  have hMz : (0 : ℤ) < ((2 * p ^ 2 : ℕ) : ℤ) := by exact_mod_cast hM
  have hclt : c < 2 := by
    by_contra hcon
    push_neg at hcon
    have := mul_le_mul_of_nonneg_left hcon hMz.le
    linarith
  have hcgt : -2 < c := by
    by_contra hcon
    push_neg at hcon
    have := mul_le_mul_of_nonneg_left hcon hMz.le
    linarith
  have hcases : c = -1 ∨ c = 0 ∨ c = 1 := by omega
  rcases hcases with rfl | rfl | rfl
  · -- `B + M = A`
    exfalso
    have heq : etMap p k₁ + etMap p k₂ = etMap p k₃ + etMap p k₄ + 2 * p ^ 2 := by
      have : ((etMap p k₃ + etMap p k₄ : ℕ) : ℤ) - ((etMap p k₁ + etMap p k₂ : ℕ) : ℤ)
          = -(2 * (p : ℤ) ^ 2) := by push_cast at hc ⊢; linarith
      have h' : ((etMap p k₁ + etMap p k₂ : ℕ) : ℤ)
          = ((etMap p k₃ + etMap p k₄ + 2 * p ^ 2 : ℕ) : ℤ) := by push_cast at this ⊢; linarith
      exact_mod_cast h'
    rw [hA, hB] at heq
    have hshift : 2 * p * (k₁ + k₂) + (k₁ ^ 2 % p + k₂ ^ 2 % p)
        = 2 * p * (k₃ + k₄ + p) + (k₃ ^ 2 % p + k₄ ^ 2 % p) := by
      have : 2 * p * (k₃ + k₄ + p) = 2 * p * (k₃ + k₄) + 2 * p ^ 2 := by ring
      omega
    obtain ⟨hS, hr⟩ :=
      base_digits_unique (m := 2 * p) (by omega)
        (by have := hmod k₁; have := hmod k₂; omega)
        (by have := hmod k₃; have := hmod k₄; omega) hshift
    exact shift_absurd hp hodd hk₃ hk₄ hk₁ hk₂ (by omega) hr.symm
  · -- genuine equality: fall back to the integer Sidon property
    have heq : etMap p k₁ + etMap p k₂ = etMap p k₃ + etMap p k₄ := by
      have : ((etMap p k₃ + etMap p k₄ : ℕ) : ℤ) - ((etMap p k₁ + etMap p k₂ : ℕ) : ℤ) = 0 := by
        simpa using hc
      have h' : ((etMap p k₁ + etMap p k₂ : ℕ) : ℤ) = ((etMap p k₃ + etMap p k₄ : ℕ) : ℤ) := by
        linarith
      exact_mod_cast h'
    exact etSet_isSidon hp hodd _ hu _ hv _ hw _ hx heq
  · -- `A + M = B`
    exfalso
    have heq : etMap p k₃ + etMap p k₄ = etMap p k₁ + etMap p k₂ + 2 * p ^ 2 := by
      have h' : ((etMap p k₃ + etMap p k₄ : ℕ) : ℤ)
          = ((etMap p k₁ + etMap p k₂ + 2 * p ^ 2 : ℕ) : ℤ) := by push_cast at hc ⊢; linarith
      exact_mod_cast h'
    rw [hA, hB] at heq
    have hshift : 2 * p * (k₃ + k₄) + (k₃ ^ 2 % p + k₄ ^ 2 % p)
        = 2 * p * (k₁ + k₂ + p) + (k₁ ^ 2 % p + k₂ ^ 2 % p) := by
      have : 2 * p * (k₁ + k₂ + p) = 2 * p * (k₁ + k₂) + 2 * p ^ 2 := by ring
      omega
    obtain ⟨hS, hr⟩ :=
      base_digits_unique (m := 2 * p) (by omega)
        (by have := hmod k₃; have := hmod k₄; omega)
        (by have := hmod k₁; have := hmod k₂; omega) hshift
    exact shift_absurd hp hodd hk₁ hk₂ hk₃ hk₄ (by omega) hr.symm
