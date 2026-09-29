-- Prove2me | Definitions.Def_Bridges_PrimeSpectralRateDistortion
-- name    : Bridges_PrimeSpectralRateDistortion
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:33:12.494614+00:00
-- url     : https://prove2.me/theorems/9a89cc2e-3a67-4b78-9003-e20f6c0d5946
-- title:
--   Aether Catalog definitions — Bridges_PrimeSpectralRateDistortion
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.PrimeSpectralRateDistortion`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/PrimeSpectralRateDistortion.lean by skeleton subtraction
import Mathlib
/-
# Prime-Spectral Rate–Distortion Theory for Finite Spectra

This file develops a constructive rate–distortion theory over finite prime spectra.
The core idea: given a finite set of "spectral states" (prime witnesses of non-derivability)
and a "gap" function measuring separation power, we find optimal codebooks—minimal
subsets of spectral states that approximate the full separation power within tolerance ε.

## Main results

* `spec_is_zero_codebook` — the full spectrum is always a 0-codebook
* `exists_optimal_codebook` — existence of a cardinality-minimal ε-codebook
* `codingNumber_mono` — rate–distortion monotonicity: more tolerance ⟹ fewer codewords
* `zero_distortion_iff_complete_separation` — zero distortion ↔ full separation preserved
* `approximate_reconstruction` — the ε-reconstruction inequality
* `reconstruction_sound` — same code profile ⟹ same restricted gap
* Greedy codebook construction with monotone distortion decrease
-/

open Finset BigOperators

noncomputable section

/-! ## Core Types -/

/-- Inverse temperature / free-energy parameter. -/
structure BetaParam where
  val : ℝ

instance : DecidableEq BetaParam := by
  intro a b
  rcases a with ⟨a⟩; rcases b with ⟨b⟩
  by_cases h : a = b
  · exact isTrue (by subst h; rfl)
  · exact isFalse (by intro hab; exact h (BetaParam.mk.inj hab))

/-- A prime spectral state: an index paired with a beta parameter. -/
abbrev PrimeBetaState (ι : Type*) := ι × BetaParam

/-- A pair of semantic objects. -/
abbrev Pair (S : Type*) := S × S

/-! ## Gap and Distortion Definitions -/

variable {S ι : Type*} [DecidableEq S] [Fintype S] [DecidableEq ι] [Fintype ι]

/-- The full spectral gap: supremum of gap values over the full spectrum. -/
def fullGap (gap : PrimeBetaState ι → Pair S → ℝ)
    (spec : Finset (PrimeBetaState ι)) (hspec : spec.Nonempty) (x : Pair S) : ℝ :=
  spec.sup' hspec (fun ω => gap ω x)

/-- The restricted gap over a sub-codebook C. Returns 0 if C is empty. -/
def restrictedGap (gap : PrimeBetaState ι → Pair S → ℝ)
    (C : Finset (PrimeBetaState ι)) (x : Pair S) : ℝ :=
  if hC : C.Nonempty then C.sup' hC (fun ω => gap ω x) else 0

/-- Distortion: the gap lost by restricting to codebook C. -/
def distortion (gap : PrimeBetaState ι → Pair S → ℝ)
    (spec : Finset (PrimeBetaState ι)) (hspec : spec.Nonempty)
    (C : Finset (PrimeBetaState ι)) (x : Pair S) : ℝ :=
  fullGap gap spec hspec x - restrictedGap gap C x

/-- Whether C is an ε-codebook: distortion ≤ ε on all training pairs. -/
def IsEpsilonCodebook (gap : PrimeBetaState ι → Pair S → ℝ)
    (spec : Finset (PrimeBetaState ι)) (hspec : spec.Nonempty)
    (pairs : Finset (Pair S)) (ε : ℝ) (C : Finset (PrimeBetaState ι)) : Prop :=
  ∀ x ∈ pairs, distortion gap spec hspec C x ≤ ε

/-- The set of admissible ε-codebooks drawn from the spectrum. -/
def admissibleCodebooks (gap : PrimeBetaState ι → Pair S → ℝ)
    (spec : Finset (PrimeBetaState ι)) (hspec : spec.Nonempty)
    (pairs : Finset (Pair S)) (ε : ℝ) : Finset (Finset (PrimeBetaState ι)) :=
  spec.powerset.filter (fun C => ∀ x ∈ pairs, distortion gap spec hspec C x ≤ ε)

/-- The coding number: minimum cardinality of an ε-codebook from spec.
    If no ε-codebook exists, returns spec.card + 1 as a sentinel. -/
def codingNumber (gap : PrimeBetaState ι → Pair S → ℝ)
    (spec : Finset (PrimeBetaState ι)) (hspec : spec.Nonempty)
    (pairs : Finset (Pair S)) (ε : ℝ) : ℕ :=
  if h : (admissibleCodebooks gap spec hspec pairs ε).Nonempty then
    ((admissibleCodebooks gap spec hspec pairs ε).image Finset.card).min'
      (Nonempty.image h _)
  else
    spec.card + 1

/-- Complete separation: the restricted gap equals the full gap on all pairs. -/
def CompleteSeparation (gap : PrimeBetaState ι → Pair S → ℝ)
    (spec : Finset (PrimeBetaState ι)) (hspec : spec.Nonempty)
    (pairs : Finset (Pair S)) (C : Finset (PrimeBetaState ι)) : Prop :=
  ∀ x ∈ pairs, restrictedGap gap C x = fullGap gap spec hspec x

/-- Total distortion over all training pairs. -/
def totalDistortion (gap : PrimeBetaState ι → Pair S → ℝ)
    (spec : Finset (PrimeBetaState ι)) (hspec : spec.Nonempty)
    (pairs : Finset (Pair S)) (C : Finset (PrimeBetaState ι)) : ℝ :=
  ∑ x ∈ pairs, distortion gap spec hspec C x

/-- Same code profile: two pairs have identical gap values on all states in C. -/
def SameCodeProfile (gap : PrimeBetaState ι → Pair S → ℝ)
    (C : Finset (PrimeBetaState ι)) (x y : Pair S) : Prop :=
  ∀ ω ∈ C, gap ω x = gap ω y

/-- Reconstruction map: returns the gap profile restricted to C. -/
def reconstruct (gap : PrimeBetaState ι → Pair S → ℝ)
    (C : Finset (PrimeBetaState ι)) (x : Pair S) :
    PrimeBetaState ι → ℝ :=
  fun ω => if ω ∈ C then gap ω x else 0

/-- Marginal gain from adding ω to codebook C. -/
def marginalGain (gap : PrimeBetaState ι → Pair S → ℝ)
    (spec : Finset (PrimeBetaState ι)) (hspec : spec.Nonempty)
    (pairs : Finset (Pair S))
    (C : Finset (PrimeBetaState ι)) (ω : PrimeBetaState ι) : ℝ :=
  totalDistortion gap spec hspec pairs C -
    totalDistortion gap spec hspec pairs (insert ω C)

/-! ## Structural Lemmas -/

set_option linter.unusedSectionVars false

variable (gap : PrimeBetaState ι → Pair S → ℝ)
variable (spec : Finset (PrimeBetaState ι))
variable (hspec : spec.Nonempty)
variable (pairs : Finset (Pair S))

/-
Monotonicity of restricted gap under inclusion of codebooks.
-/

/-
The restricted gap on a nonempty subset of spec is bounded by the full gap.
-/

/-
Distortion is nonneg when C is a nonempty subset of spec.
-/

/-
The full spectrum restricted gap equals the full gap.
-/

/-
The full spectrum is a 0-codebook.
-/

/-
The full spectrum is an ε-codebook for any ε ≥ 0.
-/

/-
ε-codebook monotonicity: if C is an ε₁-codebook and ε₁ ≤ ε₂, then C is an ε₂-codebook.
-/

/-! ## Optimal Codebook Existence -/

/-
spec is in the admissible codebooks for ε ≥ 0.
-/

/-
Admissible codebooks are nonempty when ε ≥ 0.
-/

/-
Helper: a member of admissibleCodebooks is a subset of spec.
-/

/-
Helper: a member of admissibleCodebooks is an ε-codebook.
-/

/-
**Existence of an optimal codebook on a finite spectrum.**
    For ε ≥ 0, there exists a subset of spec that is an ε-codebook with
    minimum cardinality among all admissible codebooks.
-/

/-
Admissible codebook inclusion: ε₁ ≤ ε₂ implies admissible(ε₁) ⊆ admissible(ε₂).
-/

/-
**Monotonicity of coding number**: more tolerance ⟹ fewer codewords needed.
-/

/-! ## Zero Distortion and Complete Separation -/

/-
**Zero distortion ↔ complete separation**: a codebook has zero distortion on all
    pairs iff it completely preserves the full spectral gap.
-/

/-
Total distortion is zero iff complete separation, for C ⊆ spec.
-/

/-
Total distortion is monotone: larger codebooks have smaller distortion.
-/

/-! ## Reconstruction Theorems -/

/-
**Reconstruction soundness**: pairs with the same code profile
    have the same restricted gap.
-/

/-
**Approximate reconstruction**: an ε-codebook loses at most ε separation power.
-/

/-! ## Greedy Codebook Construction -/

/-- Choose the spectral state from spec that maximizes marginal gain. -/
def greedyChoice (C : Finset (PrimeBetaState ι)) :
    PrimeBetaState ι :=
  spec.exists_max_image (fun ω => marginalGain gap spec hspec pairs C ω)
    hspec |>.choose

/-- One step of greedy construction: add the best spectral state. -/
def greedyStep (C : Finset (PrimeBetaState ι)) :
    Finset (PrimeBetaState ι) :=
  insert (greedyChoice gap spec hspec pairs C) C

/-- The k-step greedy codebook. -/
def greedyCodebook : ℕ → Finset (PrimeBetaState ι)
  | 0 => ∅
  | k + 1 => greedyStep gap spec hspec pairs (greedyCodebook k)

/-
The greedy choice is in spec.
-/

/-
Greedy codebook is a subset of spec.
-/

/-
Greedy codebook has cardinality at most k.
-/

/-
Total distortion is nonincreasing along the greedy sequence
    (under nonneg gap assumption).
-/

/-
The greedy step is at least as good as any single insertion from spec.
-/

end


