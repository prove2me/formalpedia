-- Prove2me | Definitions.Def_Probability_ErdosRenyiConnectivityUpper
-- name    : Probability_ErdosRenyiConnectivityUpper
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-17T18:03:21.874734+00:00
-- url     : https://prove2.me/theorems/ee349cbe-2341-4cd7-b0cf-29d9190df688
-- title:
--   Aether Catalog definitions — Probability_ErdosRenyiConnectivityUpper
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.ErdosRenyiConnectivityUpper`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/ErdosRenyiConnectivityUpper.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Probability_ErdosRenyiConnectivityLower
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Cut bounds and the supercritical half of the connectivity threshold

This file complements `Probability.ErdosRenyiConnectivityLower` (which proves that
`G(n, c·log n/n)` is a.a.s. *disconnected* for `c < 1`) with the *upper* half of the
threshold picture.

The mechanism is the classical **cut union bound**: a disconnected graph has a vertex
set `S` with `1 ≤ |S| ≤ n/2` across whose boundary no edge is present; the boundary of
`S` consists of `|S|·(n-|S|)` potential edges, each absent with probability `1-p`
independently.  Hence

`P(G(n,p) disconnected) ≤ ∑_{1 ≤ |S| ≤ n/2} (1-p)^{|S|(n-|S|)}`.

Feeding this into an entropy bound for binomial coefficients (`C(n,k) ≤ (e n/k)^k`,
via Stirling) and a geometric-series estimate gives the asymptotic statement: for
`p = c·log n/n` with `c > 1` the graph `G(n,p)` is a.a.s. **connected**.  Together with
`ErdosRenyi.prob_connected_log_tendsto_zero` (a.a.s. disconnected for `c < 1`) this
establishes the **sharp connectivity threshold at `p = log n / n`**, recorded in
`ErdosRenyi.connectivity_sharp_threshold`.
-/

open Finset BigOperators Filter Topology
open scoped Classical

namespace ErdosRenyi

/-! ## 1. Boundary (cut) edge sets -/

/-- The set of potential edges crossing the cut `(S, Sᶜ)`. -/
noncomputable def cutEdges {n : ℕ} (S : Finset (Fin n)) : Finset (Edge n) :=
  Finset.univ.filter (fun e => ∃ a ∈ S, ∃ b ∉ S, (e : Sym2 (Fin n)) = s(a, b))




/-! ## 2. A disconnected graph has an empty small cut -/


/-! ## 3. The cut union bound -/



/-! ## 4. Summing the cut bound -/







/-! ## 5. The supercritical half of the threshold -/






end ErdosRenyi


