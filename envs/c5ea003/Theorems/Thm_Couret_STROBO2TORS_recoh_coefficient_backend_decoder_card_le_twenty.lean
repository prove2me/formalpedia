-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_coefficient_backend_decoder_card_le_twenty
-- name    : Couret.STROBO2TORS.recoh_coefficient_backend_decoder_card_le_twenty
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:53:11.930493+00:00
-- url     : https://prove2.me/theorems/3278e670-daea-4392-a279-2061858c442a
-- title:
--   Coefficient backend has at most twenty outputs
-- statement:
--   Let $G$ be an abelian group, $H=G[2]$, $K=G[3]$, and $P_\chi(S)=\sum_{x\in S}\chi(x)$ for a complex additive character $\chi$ (so $\chi(x+y)=\chi(x)\chi(y)$). Write $Q_S$ for ordered-sum counts and $\mathcal O_B(S)=(Q_S,(P_{\chi_i}(S))_i)$ for a bank $B=(\chi_i)$. Let $I$ be a finite index type, $J$ any index type, $U\subseteq G$ finite, $R:G\to\mathbb N$, a partial half solver $h:G\to\operatorname{Option}(G)$, an index map $j:J\to I$, an additive equivalence $e:H\simeq(J\to\mathbb F_2)$, prime/depth labels $p,k:I\to\mathbb N$, support exponent encodings, and sparse observed terms indexed by $I$. If $|U|\le6$, then $$|D_{\mathrm{coeff}}(U,R,h,j,e,p,k,\mathrm{enc},\mathrm{obs})|\le20.$$ No correctness, primality, or format assumptions are required for this cardinality bound.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohCoefficientDecoder.lean, lines 98–106; source file SHA-256 27e6ca1e00cd46d60a305c7e6828a88f59094d0e4574249284c628a6c98d5074; theorem Couret.STROBO2TORS.recoh_coefficient_backend_decoder_card_le_twenty

import Aesop
import Definitions.Def_Couret_RecohCoefficientDecoder_a5265698d3d8
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
import Theorems.Thm_Couret_STROBO2TORS_recoh_checked_fast_decoder_card_le_twenty
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





variable [Fintype I]

theorem recoh_coefficient_backend_decoder_card_le_twenty
    (U : Finset G) (R : G → ℕ) (half : G → Option G)
    (index : J → I) (e : H₂ ≃+ (J → ZMod 2))
    (p k : I → ℕ) (enc : I → Finset G → List ℕ)
    (obsTerms : I → RecohSparseTerms) (hU : U.card ≤ 6) :
    (recohCoefficientBackendDecoder U R half index e p k enc obsTerms).card ≤ 20 := by sorry


end Couret.STROBO2TORS
