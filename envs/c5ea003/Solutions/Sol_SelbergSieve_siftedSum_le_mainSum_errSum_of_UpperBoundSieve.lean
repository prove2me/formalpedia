-- Prove2me | solution 1 for SelbergSieve.siftedSum_le_mainSum_errSum_of_UpperBoundSieve
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-07-29T16:19:55.054371+00:00
-- url     : https://prove2.me/submissions/bfdb8b3c-c44a-4a74-bc69-bb6569504f3c

/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Arend Mellendijk

! This file was ported from Lean 3 source module sieve
-/
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Algebra.Order.Antidiag.Nat
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Definitions.Def_Sieve_AuxResults_defs
import Definitions.Def_Sieve_Basic_defs

open scoped BigOperators ArithmeticFunction ArithmeticFunction.Moebius

open Finset Real Nat Aux BoundingSieve

open SelbergSieve

variable (s : BoundingSieve)
local notation3 "ν" => BoundingSieve.nu (self := s)
local notation3 "P" => BoundingSieve.prodPrimes (self := s)
local notation3 "a" => BoundingSieve.weights (self := s)
local notation3 "X" => BoundingSieve.totalMass (self := s)
local notation3 "A" => BoundingSieve.support (self := s)
local notation3 "𝒜" => BoundingSieve.multSum (s := s)
local notation3 "R" => BoundingSieve.rem (s := s)

-- S = ∑_{l|P, l≤√y} g(l)
-- Used in statement of the simple form of the selberg bound

local notation3 "g" => SelbergSieve.selbergTerms s

local notation "δ" => delta

-- Unused ?

-- Facts about g

open SelbergSieve in
theorem solution (μPlus : UpperBoundSieve) :
    siftedSum (s := s) ≤ X * mainSum (s := s) μPlus + errSum (s := s) μPlus := by
  apply siftedSum_le_mainSum_errSum_of_upperMoebius _ μPlus.hμPlus

-- Results about Lambda Squared Sieves

-- set_option quotPrecheck false
-- variable (s : Sieve)

-- local notation3 "ν" => Sieve.nu s
-- local notation3 "P" => Sieve.prodPrimes s
-- local notation3 "a" => Sieve.weights s
-- local notation3 "X" => Sieve.totalMass s
-- local notation3 "R" => Sieve.rem s
-- local notation3 "g" => Sieve.selbergTerms s

