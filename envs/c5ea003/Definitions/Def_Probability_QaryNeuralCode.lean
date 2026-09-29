-- Prove2me | Definitions.Def_Probability_QaryNeuralCode
-- name    : Probability_QaryNeuralCode
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:35:10.724955+00:00
-- url     : https://prove2.me/theorems/132bbaa1-85f4-457e-8f77-4c0271aeb3fe
-- title:
--   Aether Catalog definitions — Probability_QaryNeuralCode
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.QaryNeuralCode`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/QaryNeuralCode.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Neural codes over a finite alphabet: capacity, energy classes and noisy decoding

`Catalog/Novelty/NeuralCoding.lean` models a neural code as a *binary* activity
pattern `Fin N → Bool`, with capacity `2 ^ N`.  Real neurons emit a graded
number of spikes in a window, so this file replaces the binary alphabet by an
arbitrary finite alphabet of size `q` (represented as `ZMod q`, which supplies
the group structure needed for translation arguments), `0` meaning *silent*.

## Results

1. `card_qCode` — **capacity `q ^ N`.**  There are exactly `q ^ N` patterns; and
   `qary_capacity_bound` turns this into a bound on the number of distinguishable
   concepts.
2. `card_supp_eq` — the number of patterns with a *prescribed* support `S` is
   `(q - 1) ^ |S|`.
3. `card_weight_eq` — the **type class** of energy exactly `k` has
   `N.choose k * (q - 1) ^ k` members, generalising the binary `N.choose k`.
4. `card_weight_le` — the **energy-constrained capacity**: at most `k` active
   neurons gives exactly `∑_{j ≤ k} N.choose j * (q - 1) ^ j` patterns.
5. `hammingDist_eq_weight_sub`, `card_ball` — Hamming balls have the same volume
   as the energy-`≤ r` class, by translation invariance.
6. `qary_unique_decoding` — **decoding guarantee.**  A codebook of minimum
   distance `≥ 2t + 1` decodes uniquely from any received pattern within `t`
   corrupted neurons.
7. `qary_hamming_bound` — **sphere packing.**  Such a codebook has at most
   `q ^ N / ∑_{j ≤ t} N.choose j (q-1)^j` codewords.
8. `binary_specialisation` — for `q = 2` the type-class count reduces to the
   binary count `N.choose k` of the original file.
-/

namespace Catalog.Probability.NeuralCoding.Qary

open Finset

/-- A **`q`-ary neural code** on `N` neurons: each neuron emits one of `q`
graded response levels, `0` meaning silent. -/
abbrev QCode (q N : ℕ) : Type := Fin N → ZMod q

variable {q N : ℕ} [NeZero q]

/-- The **support** of a `q`-ary pattern: the set of non-silent neurons. -/
def supp (c : QCode q N) : Finset (Fin N) := univ.filter (fun i => c i ≠ 0)

/-- The **weight** (metabolic energy) of a `q`-ary pattern. -/
def weight (c : QCode q N) : ℕ := (supp c).card








/-- The **Hamming ball** of radius `r` around a pattern: all patterns reachable
by corrupting at most `r` neurons. -/
def ball (c : QCode q N) (r : ℕ) : Finset (QCode q N) :=
  univ.filter (fun x => hammingDist x c ≤ r)







end Catalog.Probability.NeuralCoding.Qary


