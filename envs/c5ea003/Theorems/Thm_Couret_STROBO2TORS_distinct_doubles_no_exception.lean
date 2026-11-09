-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_distinct_doubles_no_exception
-- name    : Couret.STROBO2TORS.distinct_doubles_no_exception
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:40:37.056224+00:00
-- url     : https://prove2.me/theorems/6b934b9b-daf6-477a-80fe-f4b7ae652e37
-- title:
--   Three distinct doubling values exclude exceptional partners
-- statement:
--   Let G be an additive commutative group with decidable equality, S a finite subset of cardinality three, and a,b,c∈G with S={a,b,c}. Suppose a+a, b+b and c+c are pairwise distinct. Then for every finite subset T of G, ExceptionalPartner(S,T) is false. Here ExceptionalPartner requires a presentation S={p,q,q+delta} with nonzero delta satisfying delta+delta=0, p+p≠q+q, an additional two-torsion translate parameter, and the specified order-three displacement/reflected presentation for T. No finiteness of the ambient group, condition on zero, or hypothesis on the cardinality of T is required.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsCardinality.lean, lines 37–45; source file SHA-256 43bb7bc977683362729a3aa2f7c214abefd9138f3283fb79ee93f0a1da784093; theorem Couret.STROBO2TORS.distinct_doubles_no_exception

import Aesop
import Definitions.Def_Couret_Strobo2TorsCardinality_32b8061f8d58
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_Strobo2TorsCore_3589e2e5b464
import Mathlib.Data.Finset.Powerset

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem distinct_doubles_no_exception (S : Finset G) (hS : S.card = 3)
    (a b c : G) (hs : S = {a, b, c})
    (hab : a + a ≠ b + b) (hac : a + a ≠ c + c) (hbc : b + b ≠ c + c) :
    ∀ T : Finset G, ¬ ExceptionalPartner S T := by sorry
















section Finite

variable [Fintype G]


















































/-! ## Exceptional offsets for a fixed nonzero 2-torsion direction

This section identifies and counts possible DIFFERENCES b-a for a fixed
direction d. These offset counts are separate from the global fibre counts
proved in Strobo2TorsEnumeration and the exceptional zero-free counts proved
in Strobo2TorsZeroFree. An offset count alone is not a count of fibres.
-/























end Finite
end Couret.STROBO2TORS
