-- Prove2me | Theorems.Thm_algebraMap_injective_of_isIntegralClosure
-- name    : algebraMap_injective_of_isIntegralClosure
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:32:18.348265+00:00
-- url     : https://prove2.me/theorems/2a2ad5d7-9e09-495d-82e4-0568461662ed
-- title:
--   algebra Map injective of is Integral Closure: algebra Map injective of is Integral Closure
-- statement:
--   In the AKLB setup, the map from `R` to the integral closure `S` of `R` in `L` is
--   injective.
--
--   Source: https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/Unramified.lean#L35-L38
-- source:
--   https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/Unramified.lean#L35-L38

module
public import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.RingTheory.DedekindDomain.Different
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.RingTheory.Unramified.Locus
public import Definitions.Def_FltRegular_NumberTheory_Unramified
set_option autoImplicit false
@[expose] public section
public section
open UniqueFactorizationMonoid Ideal
attribute [local instance] FractionRing.liftAlgebra
variable (R K L S : Type*) [CommRing R] [CommRing S] [Algebra R S] [Field K] [Field L]
    [IsDedekindDomain R] [Algebra R K] [IsFractionRing R K] [Algebra S L]
    [Algebra K L] [Algebra R L] [IsScalarTower R S L] [IsScalarTower R K L]
    [IsIntegralClosure S R L] [FiniteDimensional K L]
variable {R} {S}
omit [IsDedekindDomain R] [IsIntegralClosure S R L] [FiniteDimensional K L]
include K L

theorem algebraMap_injective_of_isIntegralClosure : Function.Injective (algebraMap R S) := by sorry
