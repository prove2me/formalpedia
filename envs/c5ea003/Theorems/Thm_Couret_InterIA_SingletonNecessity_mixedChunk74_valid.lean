-- Prove2me | Theorems.Thm_Couret_InterIA_SingletonNecessity_mixedChunk74_valid
-- name    : Couret.InterIA.SingletonNecessity.mixedChunk74_valid
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T21:07:44.716033+00:00
-- url     : https://prove2.me/theorems/d5ffb955-2b8f-438b-b79c-a23d3047df16
-- title:
--   Validity of the mixed integer relation certificates in block 74
-- statement:
--   Let B be the fixed 64-record list Couret.InterIA.SingletonNecessity.mixedChunk74 in MatchingCertificateData; its first and last stored index lists are [6, 5, 2, 3, 0, 1, 4] and [6, 1, 5, 3, 0, 4, 2], respectively. A certificate is a record (p,i,j,α), where p is a list of natural numbers, i,j are natural numbers, and α is a list of integers. Work in the additive group ℤ⁶, with standard basis e₀,…,e₅. Put ℓ₀=0 and ℓₖ=eₖ₋₁ for 1≤k≤6. Define the ordered seven-term lists L=(e₀,e₁,e₂,e₀+e₁,e₀+e₂,e₁+e₂,2e₀) and R=(e₃,e₄,e₅,e₃+e₄,e₃+e₅,e₄+e₅,2e₃). For a stored p=(p₀,…,p₆), define the ordered relation list r by concatenating (2(e₀−e₁),2(e₃−e₄),2(e₂−e₅)) with (Lₜ−Rₚₜ) for t=0,…,6 in increasing order; indices into L and R are zero-based. Every stored p has seven entries in {0,…,6}, so this gives ten relation rows with no out-of-range lookup. Then every certificate (p,i,j,α) in B passes valid true: i<j<7, the length of α equals the length of r (ten), and the integer vector identity ∑ₛ₌₀⁹ αₛrₛ=ℓᵢ−ℓⱼ holds in ℤ⁶. Equivalently, B.all (valid true)=true. These are all the checks in valid true; it performs no separate permutation or permutation-coverage test. The statement concerns this fixed list and has no variable input or additional hypothesis.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/abelian-singleton-necessity-20261104/formal/MatchingCertificateData.lean, lines 5972–5972; source file SHA-256 281f2db6030f883e89d5aa00658e16116a8de5187f3c58c3d03bf50c9b44685c; theorem Couret.InterIA.SingletonNecessity.mixedChunk74_valid

import Definitions.Def_Couret_MatchingCertificateData_656be71337d8
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Basic
import Mathlib.Data.List.Permutation
import Definitions.Def_Couret_MatchingCertificateCore_fbb5abd3e874

set_option autoImplicit false

set_option maxRecDepth 1000000

set_option maxHeartbeats 20000000

namespace Couret.InterIA.SingletonNecessity

theorem mixedChunk74_valid : mixedChunk74.all (valid true) = true := by sorry
























end Couret.InterIA.SingletonNecessity
