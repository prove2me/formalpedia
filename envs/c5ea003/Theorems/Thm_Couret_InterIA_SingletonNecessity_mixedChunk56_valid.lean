-- Prove2me | Theorems.Thm_Couret_InterIA_SingletonNecessity_mixedChunk56_valid
-- name    : Couret.InterIA.SingletonNecessity.mixedChunk56_valid
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T21:04:38.186723+00:00
-- url     : https://prove2.me/theorems/5c40acc8-f8d8-4c16-87a9-78b34b4fc502
-- title:
--   Validity of mixed integer-lattice certificates in block 56
-- statement:
--   Every certificate in the fixed explicit list Couret.InterIA.SingletonNecessity.mixedChunk56 in MatchingCertificateData satisfies the mixed certificate validity test; this list contains 64 records. A certificate is a quadruple (p,i,j,c), with p a list of natural-number indices, i,j natural numbers and c a list of integers. Work in the integer lattice ℤ⁶ with standard basis e₀,…,e₅, and put ℓ₀=0 and ℓᵣ₊₁=eᵣ for 0≤r<6. Define the ordered lists L=(e₀,e₁,e₂,e₀+e₁,e₀+e₂,e₁+e₂,2e₀) and R=(e₃,e₄,e₅,e₃+e₄,e₃+e₅,e₄+e₅,2e₃), indexed from zero. The relation list A(p) begins with 2(e₀−e₁), 2(e₃−e₄), 2(e₂−e₅), followed, in order, by Lₜ−Rₚₜ for entries of the zipped lists L and p. In this fixed block every p has seven entries in {0,…,6}, so A(p) has ten rows. For every record in the block, all three requirements hold: i<j<7; the coefficient list c has the same length as A(p); and the integer linear combination ∑ᵣ cᵣA(p)ᵣ equals ℓᵢ−ℓⱼ in ℤ⁶. These are precisely the tests in valid(true); permutation validity is not an additional test in that predicate. Equivalently, the Boolean conjunction obtained by applying valid(true) to the entire specified list is true.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/abelian-singleton-necessity-20261104/formal/MatchingCertificateData.lean, lines 4730–4730; source file SHA-256 281f2db6030f883e89d5aa00658e16116a8de5187f3c58c3d03bf50c9b44685c; theorem Couret.InterIA.SingletonNecessity.mixedChunk56_valid

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

theorem mixedChunk56_valid : mixedChunk56.all (valid true) = true := by sorry
































































































end Couret.InterIA.SingletonNecessity
