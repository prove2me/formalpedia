-- Prove2me | Definitions.Def_Novelty_AsaiLargeSieveCharacters
-- name    : Novelty_AsaiLargeSieveCharacters
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:03:45.638483+00:00
-- url     : https://prove2.me/theorems/2bd9825a-10da-4461-b9db-2193234a1628
-- title:
--   Aether Catalog definitions — Novelty_AsaiLargeSieveCharacters
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.AsaiLargeSieveCharacters`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/AsaiLargeSieveCharacters.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Novelty_AsaiLargeSieve
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

namespace AsaiCharacters

variable {q : ℕ}

/-- The eigenvalue system attached to the Dirichlet characters mod `q`. -/
noncomputable def charSystem (q : ℕ) : DirichletCharacter ℂ q → ℕ → ℂ :=
  fun χ n => χ (n : ZMod q)









end AsaiCharacters


