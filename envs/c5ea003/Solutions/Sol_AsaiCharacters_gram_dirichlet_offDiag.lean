-- Prove2me | solution 1 for AsaiCharacters.gram_dirichlet_offDiag
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T16:54:57.997383+00:00
-- url     : https://prove2.me/submissions/d20c2dcc-008d-431a-978c-beee1691105e

-- Sol generated from Novelty/AsaiLargeSieveCharacters.lean
import Mathlib
import Definitions.Def_Novelty_AsaiLargeSieve
import Definitions.Def_Novelty_AsaiLargeSieveCharacters
import Definitions.Def_Novelty_AsaiLargeSieveGram
import Definitions.Def_Novelty_AsaiSecondMoment
/-
# The abstract Asai large sieve contains the classical multiplicative large sieve

The framework of `Novelty.AsaiLargeSieve` is stated for an arbitrary finite family of
eigenvalue systems `lam : ι → ℕ → ℂ`.  This file verifies that it is not an empty abstraction:
instantiating the family with the **Dirichlet characters modulo `q`** and the eigenvalue
system `lam χ n = χ (n mod q)` recovers the classical *multiplicative large sieve inequality
at a single modulus*,

`∑_{χ mod q} |∑_{n < N} a n · χ(n)|² ≤ φ(q) · ∑_{n < N} |a n|²`   for `N ≤ q`,

which is exactly the shape of the Asai large sieve with the Petersson diagonal replaced by
the character-orthogonality diagonal `φ(q)`.

Main results:

* `AsaiCharacters.gram_dirichlet_offDiag` — for `N ≤ q` the Gram matrix of the character
  system is *exactly* diagonal on `[0,N)`; the arithmetic input is the orthogonality relation
  `∑_χ χ(a⁻¹)χ(b) = φ(q)·δ_{a,b}` together with the injectivity of `n ↦ n mod q` on `[0,q)`.
* `AsaiCharacters.largeSieve_dirichlet` — the multiplicative large sieve inequality, obtained
  from `AsaiLargeSieve.largeSieve_of_diagonal_gram`.
* `AsaiCharacters.dualLargeSieve_dirichlet` — its dual form, for free from the abstract
  duality theorem.
* `AsaiCharacters.secondMoment_dirichlet` — the corresponding second moment bound for any
  family of values admitting an approximate functional equation of length `N ≤ q` with `J`
  blocks: `∑_χ |L χ|² ≤ J² φ(q) B`.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): if the abstract criteria of the Asai framework are the right ones,
then the classical large sieve for Dirichlet characters should drop out with *no* extra
analysis — only the finite-group orthogonality relation.

Experiment (Experimenter): confirmed.  The only nontrivial step is that the character Gram
matrix is exactly diagonal when the length `N` does not exceed the modulus, which needs two
ingredients: orthogonality for unit residues, and the observation that a *non-unit* residue
kills every character, so those rows and columns vanish identically rather than contributing
an error term.  This is why `largeSieve_of_diagonal_gram` (rather than the quasi-orthogonality
criterion) is the right abstract tool: the character system has an exact diagonal Gram matrix
whose diagonal entries are `φ(q)` at units and `0` at non-units.

Analysis (Analyst): the restriction `N ≤ q` is essential and is exactly the classical one; for
`N > q` congruent residues `m ≡ n (mod q)` make the Gram matrix non-diagonal and the constant
degrades to `φ(q)·(1 + N/q)`, which is the source of the `k + N^{1+ε}`-shape constants in the
Asai setting.

Critique (Critic): the diagonal bound is stated as `≤ φ(q)` rather than `= φ(q)` because
non-unit residues genuinely give `0`; using an equality would make the statement false for
`q > 1` and `N > 1`.  The inequality is what the large sieve needs, and it is sharp at units.
-/

open Finset Complex AsaiLargeSieve

open AsaiCharacters

variable {q : ℕ}


/-- On units, `Ring.inverse` agrees with the `ZMod` inverse. -/
theorem ringInverse_eq_inv {a : ZMod q} (ha : IsUnit a) : Ring.inverse a = a⁻¹ := by
  have h : a * a⁻¹ = 1 := ZMod.mul_inv_of_unit a ha
  have h2 := Ring.inverse_mul_cancel a ha
  calc Ring.inverse a = Ring.inverse a * (a * a⁻¹) := by rw [h, mul_one]
    _ = (Ring.inverse a * a) * a⁻¹ := by ring
    _ = a⁻¹ := by rw [h2, one_mul]

/-- Complex conjugation of a character value at a unit is evaluation at the inverse. -/
theorem conj_char_apply (χ : DirichletCharacter ℂ q) {a : ZMod q} (ha : IsUnit a) :
    (starRingEnd ℂ) (χ a) = χ a⁻¹ := by
  have h1 : (starRingEnd ℂ) (χ a) = star (χ a) := rfl
  rw [h1, MulChar.star_apply' χ a, MulChar.inv_apply, ringInverse_eq_inv ha]

/-- Distinct residues below the modulus stay distinct after reduction. -/
theorem natCast_ne {m n : ℕ} (hm : m < q) (hn : n < q) (h : m ≠ n) :
    ((m : ZMod q)) ≠ (n : ZMod q) := by
  intro hc
  apply h
  have h1 : ((m : ZMod q)).val = m := ZMod.val_natCast_of_lt hm
  have h2 : ((n : ZMod q)).val = n := ZMod.val_natCast_of_lt hn
  rw [← h1, ← h2, hc]







open AsaiCharacters in
theorem solution[NeZero q] {N : ℕ} (hN : N ≤ q) {m n : ℕ}
    (hm : m ∈ Finset.range N) (hn : n ∈ Finset.range N) (hmn : m ≠ n) :
    gram (Finset.univ : Finset (DirichletCharacter ℂ q)) (charSystem q) m n = 0 := by
  have hm' : m < q := lt_of_lt_of_le (Finset.mem_range.mp hm) hN
  have hn' : n < q := lt_of_lt_of_le (Finset.mem_range.mp hn) hN
  by_cases hu : IsUnit ((n : ZMod q))
  · have hkey : ∑ χ : DirichletCharacter ℂ q, χ ((n : ZMod q))⁻¹ * χ ((m : ZMod q))
        = if ((n : ZMod q)) = ((m : ZMod q)) then (q.totient : ℂ) else 0 :=
      DirichletCharacter.sum_char_inv_mul_char_eq ℂ hu _
    rw [if_neg (fun hc => natCast_ne hn' hm' (Ne.symm hmn) hc)] at hkey
    rw [gram]
    calc ∑ χ : DirichletCharacter ℂ q,
          charSystem q χ m * (starRingEnd ℂ) (charSystem q χ n)
        = ∑ χ : DirichletCharacter ℂ q, χ ((n : ZMod q))⁻¹ * χ ((m : ZMod q)) := by
          refine Finset.sum_congr rfl fun χ _ => ?_
          rw [charSystem, charSystem, conj_char_apply χ hu]
          ring
      _ = 0 := hkey
  · rw [gram]
    refine Finset.sum_eq_zero fun χ _ => ?_
    rw [charSystem, charSystem, MulChar.map_nonunit χ hu]
    simp
