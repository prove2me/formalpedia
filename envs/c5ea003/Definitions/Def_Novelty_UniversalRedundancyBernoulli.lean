-- Prove2me | Definitions.Def_Novelty_UniversalRedundancyBernoulli
-- name    : Novelty_UniversalRedundancyBernoulli
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:46:26.714612+00:00
-- url     : https://prove2.me/theorems/48bcc80c-20b1-4952-80f0-ad1cefda61c7
-- title:
--   Aether Catalog definitions — Novelty_UniversalRedundancyBernoulli
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.UniversalRedundancyBernoulli`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/UniversalRedundancyBernoulli.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Novelty_BinomialConcentration
import Definitions.Def_Novelty_UniversalRedundancyShtarkov
/-
# The price of universality, IV: a Rissanen-style `(1/2) log₂ n` lower bound

We instantiate the exact minimax theory of `UniversalRedundancyShtarkov` on the
class of **memoryless binary sources of block length `n`**: messages are binary
strings of length `n` (encoded as subsets of `Fin n`), and the source with
parameter `t` gives the string `s` probability `t ^ #s * (1 - t) ^ (n - #s)`.
The class is indexed by the maximum-likelihood grid `t = j / n`, `j = 0, …, n`
(the standard parametrisation for normalised maximum likelihood: `j/n` is exactly
the MLE of a string with `j` ones).

The main theorem, `bernoulli_regret_ge_half_logb`, states that **every** code for
length-`n` binary strings suffers, on some string, a regret of at least

  `(1/2) · log₂ n − 2`  bits

against the best member of the class.  This reproduces Rissanen's `(k/2) log n`
minimax redundancy rate for a `k = 1`-parameter family, with explicit constants
and no asymptotics.

The proof is the classical "counting distinguishable sources" argument made
quantitative:

* the Shtarkov sum dominates `∑ᵢ Pθᵢ(Kᵢ)` for any disjoint family of index sets;
* Chebyshev's inequality (`binw_concentration`) shows that a binomial source
  with mean `c` puts mass `≥ 3/4` on the window of half-width `d ≈ √n` around `c`;
* there are `≈ √n / 2` such windows inside `[0, n]`, so the Shtarkov sum is
  `≥ √n / 4`, i.e. the class contains `≈ √n` mutually distinguishable sources.
-/

namespace PriceOfUniversality

open Finset Real

/-! ## The class of memoryless binary sources -/

/-- Messages of block length `n`: binary strings, encoded as subsets of `Fin n`
(the set of positions carrying a one). -/
abbrev Msg (n : ℕ) := Finset (Fin n)

/-- The memoryless (i.i.d. Bernoulli) source with parameter `t` on strings of
length `n`. -/
noncomputable def bern (n : ℕ) (t : ℝ) (s : Msg n) : ℝ := t ^ (#s) * (1 - t) ^ (n - #s)

/-- The class of memoryless binary sources indexed by the maximum-likelihood grid
`t = j / n`. -/
noncomputable def bernClass (n : ℕ) : Fin (n + 1) → Msg n → ℝ :=
  fun j s => bern n ((j : ℝ) / n) s






/-! ## The Shtarkov sum of the class -/

/-- The maximum likelihood of a string with `k` ones, over the grid. -/
noncomputable def mlik (n : ℕ) (k : ℕ) : ℝ :=
  (univ : Finset (Fin (n + 1))).sup' univ_nonempty
    (fun j => ((j : ℝ) / n) ^ k * (1 - (j : ℝ) / n) ^ (n - k))






/-! ## The `√n` lower bound on the Shtarkov sum -/

section Grid

variable (n : ℕ)

/-- Half-width of the concentration windows: `d ≈ √n`. -/
private noncomputable abbrev dwin : ℕ := Nat.sqrt n + 1

/-- Number of windows minus one. -/
private noncomputable abbrev nwin : ℕ := n / (2 * dwin n)

private noncomputable abbrev center (i : ℕ) : ℕ := 2 * dwin n * i

private noncomputable abbrev window (i : ℕ) : Finset ℕ :=
  (range (n + 1)).filter (fun k => k < center n i + dwin n ∧ center n i < k + dwin n)

private noncomputable abbrev gridIdx (i : ℕ) : Fin (n + 1) :=
  ⟨min (center n i) n, by omega⟩







end Grid


/-! ## Rissanen-style minimax redundancy -/




end PriceOfUniversality


