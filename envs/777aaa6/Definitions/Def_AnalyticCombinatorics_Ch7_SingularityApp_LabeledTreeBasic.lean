-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch7_SingularityApp_LabeledTreeBasic
-- name    : AnalyticCombinatorics_Ch7_SingularityApp_LabeledTreeBasic
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-28T12:08:00.766677+00:00
-- url     : https://prove2.me/theorems/19dabb2e-d0e5-446b-bff9-53c6d90fa3d9
-- title:
--   Labeled Tree Basic
-- statement:
--   The mathematical objects and operations are specified by the following source definitions.
--
--   ```lean
--   def LabeledTree (n : ℕ) : Type :=
--     {G : SimpleGraph (Fin n) // G.IsTree}
--   ```
--
--   ```lean
--   def RootedLabeledTree (n : ℕ) : Type :=
--     LabeledTree n × Fin n
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch7/SingularityApp/LabeledTreeBasic.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Labelled trees on a finite vertex set

We introduce the genuine combinatorial object underlying Cayley's formula: the
type of labelled trees on `Fin n`, namely simple graphs on `Fin n` that are
trees (connected and acyclic), and the rooted version.  These are finite types.

The cardinality results (`card (LabeledTree n) = n^(n-2)`,
`card (RootedLabeledTree n) = n^(n-1)`) and the connection to the banked
`cayleyRootedTree` are established in `Prufer.lean` / `Cayley.lean`.
-/

namespace AnalyticCombinatorics.Ch7.SingularityApp.LabeledTreeNS

/-- A labelled tree on `n` vertices: a simple graph on `Fin n` that is a tree. -/
def LabeledTree (n : ℕ) : Type :=
  {G : SimpleGraph (Fin n) // G.IsTree}

/-- A rooted labelled tree on `n` vertices. -/
def RootedLabeledTree (n : ℕ) : Type :=
  LabeledTree n × Fin n

instance instFiniteLabeledTree (n : ℕ) : Finite (LabeledTree n) := by
  unfold LabeledTree; infer_instance

noncomputable instance instFintypeLabeledTree (n : ℕ) : Fintype (LabeledTree n) :=
  Fintype.ofFinite _

noncomputable instance instFintypeRootedLabeledTree (n : ℕ) :
    Fintype (RootedLabeledTree n) := by
  unfold RootedLabeledTree; infer_instance

end AnalyticCombinatorics.Ch7.SingularityApp.LabeledTreeNS


