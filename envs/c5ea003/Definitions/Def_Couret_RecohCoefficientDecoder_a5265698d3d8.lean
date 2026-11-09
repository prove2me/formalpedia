-- Prove2me | Definitions.Def_Couret_RecohCoefficientDecoder_a5265698d3d8
-- name    : Couret_RecohCoefficientDecoder_a5265698d3d8
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:05:22.355146+00:00
-- url     : https://prove2.me/theorems/a48d68ad-d55d-403a-bdd3-d7d9216ad321
-- title:
--   Coefficient-based indexed decoding backend
-- statement:
--   Given a character index map, prime/depth data, exponent encodings and sparse observed coefficients, this defines Boolean signs by comparing each candidate reading with the observed coefficient data. A supplied additive equivalence from two-torsion to binary coordinate functions turns these signs into a translation.
--
--   The backend generates fast edge candidates, applies that indexed recovery, and filters with the full coefficient observation check. This is the executable backend whose semantic exactness is proved separately.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohCoefficientDecoder.lean; source file SHA-256 27e6ca1e00cd46d60a305c7e6828a88f59094d0e4574249284c628a6c98d5074

import Aesop
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Module.ZMod
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_RecohIndexedSignRecovery_d641979954b3
import Definitions.Def_Couret_RecohCoefficientObservations_4ffca285ab72

set_option autoImplicit false

/-!
The RECOH decoder with observed coefficients in the cyclotomic power basis.

The observed inputs are finite lists of exponent/integer-coefficient pairs,
as used by the Python observation format.  Candidate readings are generated
from root exponents and compared directly to those pairs.  No inverse map
from a coefficient polynomial to a list of roots is required.

The binary probes are selected inside the same full bank and use the same
observed inputs.  Their index type is arbitrary, allowing the actual subtype
of even cyclic coordinates rather than a noncomputable reindexing to Fin r.
-/

namespace Couret.STROBO2TORS

variable {G I J : Type*} [AddCommGroup G] [DecidableEq G]

local notation "H₂" => recohTorsionSubgroup (G := G) 2

/-- Exact equality bits against the observed integer coefficients. -/
def recohCoefficientSignBools (index : J → I) (p k : I → ℕ)
    (enc : I → Finset G → List ℕ) (obsTerms : I → RecohSparseTerms)
    (B : Finset G) : J → Bool :=
  fun j => recohCoefficientMatch (p (index j)) (k (index j))
    (enc (index j) B) (obsTerms (index j))



variable [Fintype I]

/-- Full integer-coefficient backend.  The group and its torsion subgroup
are not enumerated.  Coordinates and root encoders are supplied as data. -/
def recohCoefficientBackendDecoder
    (U : Finset G) (R : G → ℕ) (half : G → Option G)
    (index : J → I) (e : H₂ ≃+ (J → ZMod 2))
    (p k : I → ℕ) (enc : I → Finset G → List ℕ)
    (obsTerms : I → RecohSparseTerms) : Finset (Finset G) :=
  recohCheckedFastDecoder U half
    (recohIndexedRecoverSupport e (recohCoefficientSignBools index p k enc obsTerms))
    (recohCoefficientObservationCheck U R p k enc obsTerms)





end Couret.STROBO2TORS


