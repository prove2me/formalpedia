-- Prove2me | Definitions.Def_Bridges_VietorisRipsSubSqrt2LowerBound
-- name    : Bridges_VietorisRipsSubSqrt2LowerBound
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:46:35.271323+00:00
-- url     : https://prove2.me/theorems/0abc59fa-91c7-469e-8641-f9595c4281c3
-- title:
--   Aether Catalog definitions — Bridges_VietorisRipsSubSqrt2LowerBound
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.VietorisRipsSubSqrt2LowerBound`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/VietorisRipsSubSqrt2LowerBound.lean by skeleton subtraction
import Mathlib

/-!
# A cross-domain bridge: sub-√2 Vietoris–Rips approximations force exponentially many
  simplices, with an effective exponent `γ(c)` vanishing at the √2 threshold

This file connects three *a priori* separate areas around a single explicit construction:

* **Metric geometry.**  We build, for every `n`, a genuine finite metric space on
  `Fin n` — in fact an *ultrametric* — whose non-zero distances are graded through the
  window `[1, √2]` (`dist_isMetric`: symmetry, non-negativity, vanishing on the diagonal,
  and the (strong) triangle inequality).

* **Topological data analysis / interleavings.**  The Vietoris–Rips complex `VRcomplex`
  is the flag complex of the proximity relation; a `c`-approximation `IsCApprox` is a
  one-sided multiplicative interleaving of simplicial filtrations, the standard notion of a
  finitely-presented `c`-approximation used by approximation algorithms in TDA.

* **Extremal / enumerative combinatorics.**  A metric *clique* of size `m` at scale `r`
  forces `2 ^ m` simplices into `VRcomplex` (`two_pow_card_le_card_VRcomplex`): the whole
  power set of the clique is present.  This is the counting engine converting geometry into
  exponential complexity.

## The theorem (the connector)

For every `c ∈ [1, √2)` and every `n`, **any** `c`-approximation `G` of the Vietoris–Rips
filtration of `metricD n` stores at least `2 ^ ⌊γ(c) · n⌋` simplices at scale `√2`, where

  `γ(c) = (√2 / c − 1) / (√2 − 1)`

is effectively computable, satisfies `0 < γ(c) ≤ 1` on `[1, √2)`, and
`lim_{c → √2⁻} γ(c) = 0` (`gamma_tendsto_nhdsWithin`).  Thus the guaranteed exponential
rate degrades continuously to `0` exactly as the approximation factor approaches the
sharp √2 threshold, and no non-trivial rate survives at `c = √2`.

## Main results

* `dist_isMetric` — `metricD n` is a genuine (ultra)metric on `Fin n`.
* `two_pow_card_le_card_VRcomplex` — clique ⇒ exponentially many simplices (the bridge).
* `two_pow_activeCard_le_VRcomplex` — the graded active set is such a clique.
* `gamma_pos`, `gamma_le_one`, `gamma_tendsto_nhdsWithin` — the effective exponent and its
  behaviour at the √2 threshold.
* `floor_gamma_le_exponent` — the active set realises the rate `⌊γ(c) · n⌋`.
* `approx_card_lower_bound` — any `c`-approximation has `2 ^ (exponent c n)` simplices at
  scale `√2`.
* `subSqrt2_exponential_lower_bound` — **headline connector**: the explicit
  `2 ^ ⌊γ(c) · n⌋` lower bound together with `0 < γ(c) ≤ 1` and the vanishing limit.
-/

noncomputable section

open Finset Classical

namespace VRSubSqrt2

/-! ## The graded ultrametric -/

/-- Graded radius of vertex `i` among `n` points: `1 + (√2 − 1)·(i+1)/n`, so radii sweep
the window `(1, √2]` as `i` runs over `0, …, n-1`. -/
def radius (n i : ℕ) : ℝ := 1 + (Real.sqrt 2 - 1) * ((i : ℝ) + 1) / (n : ℝ)

/-- The dissimilarity: distinct points `i ≠ j` are at distance equal to the larger of
their two radii, i.e. `radius n (max i j)`; equal points are at distance `0`. -/
def metricD (n : ℕ) (i j : Fin n) : ℝ :=
  if i = j then 0 else radius n (max (i : ℕ) (j : ℕ))

/-- A subset `S` is a Vietoris–Rips simplex at scale `r` when every pair of its vertices is
within `r`. -/
def IsVRsimplex {n : ℕ} (r : ℝ) (S : Finset (Fin n)) : Prop :=
  ∀ i ∈ S, ∀ j ∈ S, metricD n i j ≤ r

/-- The Vietoris–Rips complex at scale `r`: the finite set of all its simplices. -/
def VRcomplex (n : ℕ) (r : ℝ) : Finset (Finset (Fin n)) :=
  (Finset.univ : Finset (Fin n)).powerset.filter (fun S => IsVRsimplex r S)

/-- A one-sided multiplicative `c`-approximation (interleaving) of the Vietoris–Rips
filtration: every genuine simplex at scale `t` appears in the presentation `G` by scale
`c·t`, and `G` never invents simplices absent by scale `c·t`. -/
def IsCApprox (n : ℕ) (c : ℝ) (G : ℝ → Finset (Finset (Fin n))) : Prop :=
  1 ≤ c ∧
  (∀ t, 0 ≤ t → VRcomplex n t ⊆ G (c * t)) ∧
  (∀ t, 0 ≤ t → G t ⊆ VRcomplex n (c * t))

/-! ## Basic radius facts -/





/-! ## `metricD` is a genuine (ultra)metric -/






/-! ## Clique ⇒ exponentially many simplices (the counting bridge) -/



/-! ## The graded active set is a clique -/

/-- The active set at scale `r`: the vertices whose radius is `≤ r`. -/
def activeSet (n : ℕ) (r : ℝ) : Finset (Fin n) :=
  (Finset.univ : Finset (Fin n)).filter (fun i => radius n (i : ℕ) ≤ r)



/-! ## The effective exponent `γ(c)` -/

/-- The effective exponential rate `γ(c) = (√2 / c − 1)/(√2 − 1)`. -/
def gamma (c : ℝ) : ℝ := (Real.sqrt 2 / c - 1) / (Real.sqrt 2 - 1)




/-- The exponent guaranteed at the analysis scale `√2`: the size of the active set at the
interleaved scale `√2 / c`. -/
def exponent (c : ℝ) (n : ℕ) : ℕ := (activeSet n (Real.sqrt 2 / c)).card



/-! ## The approximation lower bound -/


/-! ## Headline connector -/


end VRSubSqrt2


