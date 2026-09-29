-- Prove2me | Definitions.Def_Shared_CyclicTypeChannel
-- name    : Shared_CyclicTypeChannel
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T07:35:31.967126+00:00
-- url     : https://prove2.me/theorems/e2c026ea-9133-4bae-84eb-badbe013cc97
-- title:
--   Aether Catalog definitions — Shared_CyclicTypeChannel
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.CyclicTypeChannel`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/CyclicTypeChannel.lean by skeleton subtraction
import Mathlib
/-
# The cyclic splitting-type channel

A self-contained, formally verified account of the *splitting-type channel* of a
cyclic field extension.

For a prime `f` the Galois group of `ℚ(ζ_f)/ℚ` is `(ℤ/f)ˣ ≅ C n` with `n = f - 1`.
Writing an unramified prime `p` as `g ^ a` for a fixed generator `g`, the residue
degree (= the order of the Frobenius `p mod f`) is

  `T(p) = ord_f(p) = n / gcd(a, n)`.

This file develops:

* a general finite (counting) Shannon-entropy framework `uEnt`, its conditional
  version `condEnt` and the mutual information `mutInfo`;
* the general structural facts: the Shannon form of `uEnt`, non-negativity, the
  `log₂ |s|` cap, and the *data-processing* inequality for deterministic
  coarsenings;
* the group-theoretic grounding: `orderOf (g ^ a) = ordType n a` for a generator
  `g` of a cyclic group of order `n`, and the exact type-count law
  `#{a : ordType n a = d} = φ d`;
* exact closed-form evaluations of the type channel and of the *type-pair
  channel* of a semiprime for `n = 2, 4, 6, 10, 12, 16`, culminating in the
  headline fact that the pair channel of `C₄` and `C₆` carries strictly more
  than one bit.
-/

namespace CyclicTypeChannel

open Finset

/-! ## 1. A counting Shannon-entropy framework -/

variable {α β γ : Type*}

/-- The Shannon entropy (in bits) of the push-forward of the uniform distribution
on the finite set `s` along `g`, written as an average of fibre sizes:
`H(g) = log₂ |s| - (1/|s|) ∑_{a ∈ s} log₂ |g⁻¹(g a)|`. -/
noncomputable def uEnt [DecidableEq β] (s : Finset α) (g : α → β) : ℝ :=
  Real.logb 2 s.card - (∑ a ∈ s, Real.logb 2 (#{x ∈ s | g x = g a} : ℝ)) / s.card

/-- The conditional entropy `H(g | k)`: the average of the entropies of `g` on
the fibres of `k`, weighted by the size of the fibre. -/
noncomputable def condEnt [DecidableEq β] [DecidableEq γ]
    (s : Finset α) (g : α → β) (k : α → γ) : ℝ :=
  ∑ c ∈ s.image k, ((#{x ∈ s | k x = c} : ℝ) / s.card) * uEnt {x ∈ s | k x = c} g

/-- The mutual information `I(g ; k) = H(g) - H(g | k)`. -/
noncomputable def mutInfo [DecidableEq β] [DecidableEq γ]
    (s : Finset α) (g : α → β) (k : α → γ) : ℝ :=
  uEnt s g - condEnt s g k

section General

variable [DecidableEq β] {s : Finset α} {g : α → β}











end General

/-! ## 2. The splitting type of a cyclic Frobenius -/

/-- The **splitting type** (residue degree) attached to the exponent `a`: the order
of `g ^ a` in a cyclic group of order `n`. For `Q(ζ_f)` with `f` prime and
`n = f - 1` this is `ord_f(p) = T(p)`, the complete splitting type of `p`. -/
def ordType (n a : ℕ) : ℕ := n / Nat.gcd a n






/-! ## 3. The type channel and the semiprime type-pair channel -/

/-- The residues (exponents) of the two prime factors of a semiprime. -/
def box (n : ℕ) : Finset (ℕ × ℕ) := range n ×ˢ range n

/-- The **unordered** splitting-type pair `{T(p), T(q)}` of a semiprime `N = p q`. -/
def typePair (n : ℕ) (p : ℕ × ℕ) : ℕ × ℕ :=
  (min (ordType n p.1) (ordType n p.2), max (ordType n p.1) (ordType n p.2))

/-- The residue of the semiprime `N = p q` itself: exponents add. -/
def prodRes (n : ℕ) (p : ℕ × ℕ) : ℕ := (p.1 + p.2) % n

/-- The root-count read-out of a splitting type: the number of roots of the
cyclotomic polynomial mod `p`, i.e. `n` if `p` splits completely and `0`
otherwise. -/
def rootCount (n T : ℕ) : ℕ := if T = 1 then n else 0

/-- The `s`-projection of a type pair: how many of the two primes split
completely. -/
def sProj (t : ℕ × ℕ) : ℕ := (if t.1 = 1 then 1 else 0) + (if t.2 = 1 then 1 else 0)

/-- Entropy of the splitting type of a single prime. -/
noncomputable def typeEntropy (n : ℕ) : ℝ := uEnt (range n) (ordType n)

/-- Entropy of the unordered type pair of a semiprime. -/
noncomputable def pairEntropy (n : ℕ) : ℝ := uEnt (box n) (typePair n)

/-- Entropy of the unordered type pair given the residue of the semiprime. -/
noncomputable def condPairEntropy (n : ℕ) : ℝ := condEnt (box n) (typePair n) (prodRes n)

/-- The **type-pair channel** `I({T(p),T(q)} ; N mod f)`. -/
noncomputable def Ipair (n : ℕ) : ℝ := mutInfo (box n) (typePair n) (prodRes n)

/-- The split-count (`s`-projection) channel `I(s ; N mod f)`. -/
noncomputable def Isplit (n : ℕ) : ℝ := mutInfo (box n) (sProj ∘ typePair n) (prodRes n)










/-! ## 4. Base-two logarithms of the numerals that occur -/




















/-! ## 5. Faithfulness of the exponent model, and the exact `φ`-law for `H(T)` -/








end CyclicTypeChannel


