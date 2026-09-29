-- Prove2me | Definitions.Def_Shared_ReverseMath_Implications
-- name    : Shared_ReverseMath_Implications
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T15:13:19.851766+00:00
-- url     : https://prove2.me/theorems/60b874f4-34ef-4561-b8bf-5508ec903313
-- title:
--   Aether Catalog definitions — Shared_ReverseMath_Implications
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.ReverseMath.Implications`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/ReverseMath/Implications.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Shared_ReverseMath_Defs
/-
# Reverse Mathematics: Implications Between Ramsey-Theoretic Principles

This module proves the key structural implications in the reverse mathematics
hierarchy of Ramsey's theorem for pairs.

## Main results

* `rt1_2_bool_proof` — RT¹₂ is provable (infinite pigeonhole for Bool)
* `rt2_2_implies_rt1_2_bool` — RT²₂ → RT¹₂ via the min-coloring reduction
* `rt2_2_implies_srt2_2` — RT²₂ → SRT²₂ (trivially)
* `rt2_2_proof` — RT²₂ is provable (infinite Ramsey theorem for pairs)
* `srt2_2_implies_rt1_2_bool` — SRT²₂ → RT¹₂ via the stable reduction

## The reverse mathematics hierarchy

In the standard hierarchy RCA₀ < WKL₀ < ACA₀, these principles satisfy:
- RCA₀ ⊢ RT¹₂ (pigeonhole is computable)
- RT²₂ is strictly between WKL₀ and ACA₀ (Seetapun 1995, Liu 2012)
- SRT²₂ + COH ↔ RT²₂ (Cholak–Jockusch–Slaman 2001)

We formalize the combinatorial content of these implications in CIC+Classical.
-/

open Set Filter

/-! ## Theorem 1: RT¹₂ (Infinite Pigeonhole Principle) -/

/-
!-- The infinite pigeonhole principle for Bool: if ℕ is 2-colored, one color
class is infinite. Proof by contradiction: if both preimages are finite,
their union covers ℕ, contradicting infiniteness of ℕ. -- !--

**RT¹₂ is provable**: every `Bool`-coloring of `ℕ` has an infinite
    monochromatic class.
-/

/-
**Generalization**: RT¹ₖ holds for all `k ≥ 1`.
-/

/-
**Boundary**: RT¹₀ is vacuously true (no `ℕ → Fin 0` exists), so the
    meaningful boundary is: for `k ≥ 1`, we cannot guarantee a *specific*
    color class is infinite.
-/

/-! ## Theorem 2: RT²₂ → RT¹₂ (The Canonical Reduction) -/

/-
!-- Given f : ℕ → Bool, define the pair coloring c(i,j) = f(min i j).
If H is infinite homogeneous for c with color b, then for any i ∈ H,
pick j ∈ H with j > i; then f(i) = f(min i j) = c(i,j) = b.
So H is monochromatic for f. -- !--

The min-coloring reduction preserves monochromaticity:
    if `H` is homogeneous for `pairColoringOfUnary f`, then `H` is
    monochromatic for `f`.
-/

/-
**RT²₂ implies RT¹₂**: the structural reduction.
-/

/-- **Generalization**: RT²ₖ → RT¹ₖ for arbitrary `k`. -/
def RT2_k (k : ℕ) [NeZero k] : Prop :=
  ∀ c : ℕ → ℕ → Fin k, (∀ i j, c i j = c j i) → (∀ i, c i i = 0) →
    ∃ S : Set ℕ, ∃ b : Fin k, S.Infinite ∧ ∀ i ∈ S, ∀ j ∈ S, i ≠ j → c i j = b



/-! ## Theorem 3: RT²₂ is provable (Infinite Ramsey for Pairs) -/

/-
!-- Proof by the iterative Erdős–Rado construction:
1. Start with S₀ = ℕ, pick a₀ ∈ S₀.
2. Partition S₀ \ {a₀} by color c(a₀, ·); by RT¹₂ one class is infinite → S₁.
3. Pick a₁ ∈ S₁, repeat.
4. Get a₀ < a₁ < ... and colors d₀, d₁, ...
5. By RT¹₂ for the sequence (dᵢ), extract a monochromatic subsequence.
6. The corresponding elements form an infinite homogeneous set. -- !--

**RT²₂ is provable in CIC + Classical**: the infinite Ramsey theorem
    for pairs with 2 colors.
-/

/-! ## Theorem 4: SRT²₂ and Its Relationship to RT²₂ -/

/-
!-- SRT²₂ is the restriction of RT²₂ to stable colorings.
Since stable colorings are a special case, RT²₂ → SRT²₂ is trivial.
The converse (with COH) is the Cholak–Jockusch–Slaman decomposition. -- !--

**RT²₂ implies SRT²₂**: trivial since SRT²₂ is a restriction.
-/

/-
**SRT²₂ implies RT¹₂**: stable reduction from pigeonhole to pairs.
    Given `f : ℕ → Bool`, define `c(i,j) = f(min i j)`. This coloring is
    stable because for fixed `i`, `c(i,j) = f(i)` for all `j > i`.
    Then apply SRT²₂.
-/

/-
**Generalization (Cholak–Jockusch–Slaman decomposition)**:
    SRT²₂ + COH → RT²₂. This is the deep direction of the equivalence.
-/


/-! ## Summary: the implication diagram

  RT²₂ ——→ SRT²₂ ——→ RT¹₂
   |                    ↑
   |                    |
   +————→ RT¹₂ ————————+
           ↑
   RT²₂ ↔ SRT²₂ + COH (Cholak–Jockusch–Slaman)

  All arrows are strict over RCA₀ (except the last equivalence).
-/


