-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.simplexCount_sub_eq_sum_mixedCorrelation
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:29:30.190063+00:00
-- url     : https://prove2.me/submissions/03e06b5e-5b95-4406-bdde-7a9a6651a48a

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_ArithmeticProgression_Count
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Simplex
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_LinearForms_Basic
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_SimplexTelescoping
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Theorems.Thm_Wikipedia_SzemeredisTheorem_simplexWeight_sub_eq_sum_mixed

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section


/-!
# Elementary finite Bonferroni bounds

This file records the first two truncations of inclusion--exclusion for a
finite family of zero--one real-valued functions.  The upper bound deliberately
sums ordered pairs of distinct indices; this is a harmless factor-two
overcount that avoids choosing an order on the index type.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-- A normalized finite mean commutes with a finite sum. -/
theorem mean_finset_sum {α κ : Type*}
    [Fintype α]
    (s : Finset κ) (f : κ → α → ℝ) :
    mean (fun x => ∑ q ∈ s, f q x) =
      ∑ q ∈ s, mean (f q) := by
  simpa [mean] using
    (Finset.expect_sum_comm
      (s := (Finset.univ : Finset α)) s
      (fun x q => f q x))





end Wikipedia.SzemeredisTheorem

end
/-!
# Edge-by-edge telescoping for weighted simplex counts

The relative counting lemma compares two products by replacing one edge at a
time.  This file isolates that exact finite algebra.  No boundedness is
required: all analytic work is reduced to bounding one mixed correlation for
each edge colour.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators

open Wikipedia.SzemeredisTheorem in
/-- Exact telescoping identity for normalized simplex counts. -/
theorem solution
    {k : ℕ} {V : Fin k → Type*}
    [∀ i, Fintype (V i)]
    (H G : WeightedSimplexSystem V) :
    H.simplexCount - G.simplexCount =
      ∑ j : Fin k, mixedSimplexCorrelation H G j := by
  rw [WeightedSimplexSystem.simplexCount,
    WeightedSimplexSystem.simplexCount, ← mean_sub]
  calc
    mean (fun x => H.simplexWeight x - G.simplexWeight x) =
        mean (fun x =>
          ∑ j : Fin k, mixedSimplexTerm H G j x) := by
      apply congrArg mean
      funext x
      exact simplexWeight_sub_eq_sum_mixed H G x
    _ = ∑ j : Fin k, mean (mixedSimplexTerm H G j) :=
      mean_finset_sum Finset.univ
        (fun j => mixedSimplexTerm H G j)
    _ = ∑ j : Fin k, mixedSimplexCorrelation H G j := by
      rfl
