-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_coefficient_sign_bools_exact
-- name    : Couret.STROBO2TORS.recoh_coefficient_sign_bools_exact
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:49:27.053179+00:00
-- url     : https://prove2.me/theorems/88b78ecf-b61e-4be2-be5b-97066fc0b6d8
-- title:
--   The coefficient sign Boolean means exact equality of a selected reading
-- statement:
--   Let $G$ be an abelian group, $I$ an index type, $p_i$ primes, $k_i\in\mathbb N$, and $\zeta_i$ primitive roots of order $p_i^{k_i+1}$. Let $\chi_i$ be complex additive characters, $L_i$ reduced sparse observed lists, and $v_i=\sum_{(e,c)\in L_i}c\zeta_i^e$. An exponent encoder $E_i(B)$ interprets as $\sum_{e\in E_i(B)}\zeta_i^e=P_{\chi_i}(B)$ for each support to which the assumption is applied. Assume the encoder interpretation holds for every finite support. Let $J$ be any type and $\iota:J\to I$ any index map. For any support $B$ and $j\in J$,
--
--   $$\operatorname{signBool}(B,j)=\mathrm{true}\iff v_{\iota(j)}=P_{\chi_{\iota(j)}}(B).$$
--
--   No finite-index or nonvanishing assumption is needed for this equality test.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohCoefficientDecoder.lean, lines 32–49; source file SHA-256 27e6ca1e00cd46d60a305c7e6828a88f59094d0e4574249284c628a6c98d5074; theorem Couret.STROBO2TORS.recoh_coefficient_sign_bools_exact

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
import Theorems.Thm_Couret_STROBO2TORS_recoh_coefficient_match_iff
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

omit [DecidableEq G] in

theorem recoh_coefficient_sign_bools_exact
    (index : J → I) (p k : I → ℕ)
    (enc : I → Finset G → List ℕ) (obsTerms : I → RecohSparseTerms)
    (bank : I → AddChar G ℂ) (ζ obs : I → ℂ)
    (hp : ∀ i, (p i).Prime)
    (hζ : ∀ i, IsPrimitiveRoot (ζ i) ((p i) ^ (k i + 1)))
    (hred : ∀ i, RecohCoefficientsReduced (p i) (k i) (obsTerms i))
    (henc : ∀ i B, ((enc i B).map ((ζ i) ^ ·)).sum = recohSupportProbe (bank i) B)
    (hobs : ∀ i, recohCoefficientValue (ζ i) (obsTerms i) = obs i)
    (B : Finset G) (j : J) :
    recohCoefficientSignBools index p k enc obsTerms B j = true ↔
      obs (index j) = recohSupportProbe (bank (index j)) B := by sorry


variable [Fintype I]







end Couret.STROBO2TORS
