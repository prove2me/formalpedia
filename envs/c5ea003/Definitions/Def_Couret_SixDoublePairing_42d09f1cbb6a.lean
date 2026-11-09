-- Prove2me | Definitions.Def_Couret_SixDoublePairing_42d09f1cbb6a
-- name    : Couret_SixDoublePairing_42d09f1cbb6a
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:00:20.869847+00:00
-- url     : https://prove2.me/theorems/7b5ad2e6-a249-46d3-a69e-49a4fc703d62
-- title:
--   Parity and all pairings of six values
-- statement:
--   For six values $d_0,\ldots,d_5$, fibre parity means that every value occurs with equal parity in the first and last triples. The pairing predicate explicitly lists all fifteen partitions of the six indices into three pairs, requiring equal values within each pair.
--
--   These predicates formulate the finite combinatorial bridge from parity equality to an equal-value matching, without requiring a group structure on the values.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/abelian-singleton-necessity-20261104/formal/SixDoublePairing.lean; source file SHA-256 e79e5620a66aef560a893ef2c2f1adb2de1fc3f858804fed5dd6dbd8a3babec4

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_ConvolutionParity_aa654fd002fc
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
namespace Couret.InterIA.SingletonNecessity
def FibreParity {α : Type*} [DecidableEq α] (d : Fin 6 → α) : Prop :=
  ∀ z, ((if d 0=z then 1 else 0)+(if d 1=z then 1 else 0)+(if d 2=z then 1 else 0) : ℕ)%2 =
    ((if d 3=z then 1 else 0)+(if d 4=z then 1 else 0)+(if d 5=z then 1 else 0) : ℕ)%2
def HasPairing {α : Type*} (d : Fin 6 → α) : Prop :=
  (d 0=d 1 ∧ d 2=d 3 ∧ d 4=d 5) ∨
  (d 0=d 1 ∧ d 2=d 4 ∧ d 3=d 5) ∨
  (d 0=d 1 ∧ d 2=d 5 ∧ d 3=d 4) ∨
  (d 0=d 2 ∧ d 1=d 3 ∧ d 4=d 5) ∨
  (d 0=d 2 ∧ d 1=d 4 ∧ d 3=d 5) ∨
  (d 0=d 2 ∧ d 1=d 5 ∧ d 3=d 4) ∨
  (d 0=d 3 ∧ d 1=d 2 ∧ d 4=d 5) ∨
  (d 0=d 3 ∧ d 1=d 4 ∧ d 2=d 5) ∨
  (d 0=d 3 ∧ d 1=d 5 ∧ d 2=d 4) ∨
  (d 0=d 4 ∧ d 1=d 2 ∧ d 3=d 5) ∨
  (d 0=d 4 ∧ d 1=d 3 ∧ d 2=d 5) ∨
  (d 0=d 4 ∧ d 1=d 5 ∧ d 2=d 3) ∨
  (d 0=d 5 ∧ d 1=d 2 ∧ d 3=d 4) ∨
  (d 0=d 5 ∧ d 1=d 3 ∧ d 2=d 4) ∨
  (d 0=d 5 ∧ d 1=d 4 ∧ d 2=d 3)

end Couret.InterIA.SingletonNecessity


