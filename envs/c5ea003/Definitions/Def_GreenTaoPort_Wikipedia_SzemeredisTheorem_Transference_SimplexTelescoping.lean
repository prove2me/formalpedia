-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_SimplexTelescoping
-- name    : GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_SimplexTelescoping
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T05:51:17.52733+00:00
-- url     : https://prove2.me/theorems/b3efa758-d7b4-4e96-aed5-1221457bf124
-- title:
--   Mixed correlations for edge-by-edge simplex replacement
-- statement:
--   Let $H$ and $G$ be real-weighted partite simplex systems with $k$ edge colours. For a full vertex assignment $x$, the mixed term at colour $j$ is
--
--   $$
--   (H_j-G_j)(x_{-j})
--   \prod_{i<j}H_i(x_{-i})
--   \prod_{i>j}G_i(x_{-i}),
--   $$
--
--   where $x_{-i}$ deletes coordinate $i$. Thus earlier colours use $H$, later colours use $G$, and colour $j$ contributes their difference. For finite vertex types, the mixed correlation is the normalized mean of this term. The correlation-bound predicate requires the absolute value of every mixed correlation to be at most a real parameter $\varepsilon$. These definitions impose no positivity or boundedness on the edge weights.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Transference/SimplexTelescoping.lean#L47-L125

import Mathlib.Algebra.BigOperators.Ring.Finset
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Simplex
import Lean
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Edge-by-edge telescoping for weighted simplex counts

The relative counting lemma compares two products by replacing one edge at a
time.  This file isolates that exact finite algebra.  No boundedness is
required: all analytic work is reduced to bounding one mixed correlation for
each edge colour.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators



/-- The mixed term produced while replacing edge colour `j`: earlier
colours come from `H`, later colours from `G`, and colour `j` contributes
their difference. -/
def mixedSimplexTerm {k : ℕ} {V : Fin k → Type*}
    (H G : WeightedSimplexSystem V) (j : Fin k)
    (x : (i : Fin k) → V i) : ℝ :=
  (H.edgeWeight j (deleteCoordinate x j) -
      G.edgeWeight j (deleteCoordinate x j)) *
    (∏ i ∈ (Finset.univ : Finset (Fin k)) with i < j,
      H.edgeWeight i (deleteCoordinate x i)) *
    ∏ i ∈ (Finset.univ : Finset (Fin k)) with j < i,
      G.edgeWeight i (deleteCoordinate x i)



/-- The normalized mixed correlation attached to one edge replacement. -/
noncomputable def mixedSimplexCorrelation
    {k : ℕ} {V : Fin k → Type*}
    [∀ i, Fintype (V i)]
    (H G : WeightedSimplexSystem V) (j : Fin k) : ℝ :=
  mean (mixedSimplexTerm H G j)





/-- Every mixed edge-replacement correlation is at most `ε`. -/
def MixedSimplexCorrelationLe
    {k : ℕ} {V : Fin k → Type*}
    [∀ i, Fintype (V i)]
    (H G : WeightedSimplexSystem V) (ε : ℝ) : Prop :=
  ∀ j, |mixedSimplexCorrelation H G j| ≤ ε



end Wikipedia.SzemeredisTheorem


/- Materialize compiler-generated declarations promised by this bundle. -/
run_meta do
  for requiredName in #[
    `Wikipedia.SzemeredisTheorem.mixedSimplexTerm.eq_1
  ] do
    let actualName ← Lean.realizeGlobalConstNoOverloadCore requiredName
    unless actualName == requiredName do
      throwError "Generated companion resolved to an unexpected name"


