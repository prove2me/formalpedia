-- Prove2me | Theorems.Thm_Catalog_Probability_NeuralCoding_Qary_card_supp_eq
-- name    : Catalog.Probability.NeuralCoding.Qary.card_supp_eq
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:00:20.430463+00:00
-- url     : https://prove2.me/theorems/46457317-8c34-4b54-a458-781ce0579961
-- title:
--   Patterns with a prescribed support.
-- statement:
--   **Patterns with a prescribed support.**  Exactly `(q - 1) ^ |S|` patterns
--   have support `S`.
--
--   ```lean
--   theorem Catalog.Probability.NeuralCoding.Qary.card_supp_eq(S : Finset (Fin N)) :
--       (univ.filter (fun c : QCode q N => supp c = S)).card = (q - 1) ^ S.card := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/QaryNeuralCode.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/QaryNeuralCode.lean#L70

-- Thm stub generated from Probability/QaryNeuralCode.lean
import Mathlib
import Definitions.Def_Probability_QaryNeuralCode
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

open Catalog.Probability.NeuralCoding.Qary

open Finset


variable {q N : ℕ} [NeZero q]

theorem Catalog.Probability.NeuralCoding.Qary.card_supp_eq(S : Finset (Fin N)) :
    (univ.filter (fun c : QCode q N => supp c = S)).card = (q - 1) ^ S.card := by sorry
