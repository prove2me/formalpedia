-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_coefficient_backend_decoder_eq_exact
-- name    : Couret.STROBO2TORS.recoh_coefficient_backend_decoder_eq_exact
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:02:37.430645+00:00
-- url     : https://prove2.me/theorems/fc767125-59a4-4823-affa-ef966a0e9752
-- title:
--   The coefficient backend equals exact decoding
-- statement:
--   Let $G$ be a finite abelian group. For a character $\chi:G\to\mathbb C$ write $P_\chi(S)=\sum_{x\in S}\chi(x)$, and for a bank $(\chi_i)$ write $\operatorname{Obs}(S)=(Q_S,(P_{\chi_i}(S))_i)$, where $Q_S(z)$ counts ordered pairs from $S$ summing to $z$. The exact decoder of $(R,o)$ consists of all three-element supports $S$ with $\operatorname{Obs}(S)=(R,o)$. Let $I$ be a finite measurement index set and $J$ any coordinate index set. Let $e:G[2]\cong\mathbb F_2^J$ be additive and let $\iota:J\to I$. Let $U\subseteq G$, $R:G\to\mathbb N$, and suppose $R(z)\ne0$ implies $z\in U$. A halving function is sound when every returned $\sigma$ satisfies $2\sigma=t$, and complete when it returns some half whenever one exists. For every $i$, let $p_i$ be prime, $k_i\in\mathbb N$, and $\zeta_i$ primitive of order $p_i^{k_i+1}$. Let a support encoding $E_i(B)$ satisfy $\sum_{a\in E_i(B)}\zeta_i^a=P_{\chi_i}(B)$ for every finite $B$, and let a sparse coefficient list $T_i$ have exponents below $(p_i-1)p_i^{k_i}$ and value $o_i=\sum_{(a,c)\in T_i}c\zeta_i^a$. Assume $\chi_{\iota(j)}(u)=(-1)^{e(u)_j}$ for $u\in G[2]$, and $P_{\chi_{\iota(j)}}(B)\ne0$ for every three-set $B$ and $j\in J$. For a sound and complete halving function, the coefficient backend, which obtains translation signs from coefficient comparisons and then checks the full observation, satisfies
--
--   $$\operatorname{CoefficientBackend}(U,R,h,\iota,e,p,k,E,T)=\operatorname{ExactDecoder}(R,o).$$
--
--   This identifies executable coefficient filtering with the semantic solution set.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohCoefficientDecoder.lean, lines 64–96; source file SHA-256 27e6ca1e00cd46d60a305c7e6828a88f59094d0e4574249284c628a6c98d5074; theorem Couret.STROBO2TORS.recoh_coefficient_backend_decoder_eq_exact

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
import Theorems.Thm_Couret_STROBO2TORS_recoh_coefficient_observation_check_iff
import Theorems.Thm_Couret_STROBO2TORS_recoh_coefficient_sign_bools_exact
import Theorems.Thm_Couret_STROBO2TORS_recoh_indexed_checked_decoder_eq_exact
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

theorem recoh_coefficient_backend_decoder_eq_exact [Fintype G]
    (U : Finset G) (R : G → ℕ) (half : G → Option G)
    (index : J → I) (e : H₂ ≃+ (J → ZMod 2))
    (p k : I → ℕ) (enc : I → Finset G → List ℕ)
    (obsTerms : I → RecohSparseTerms)
    (bank : I → AddChar G ℂ) (ζ obs : I → ℂ)
    (hhalf : RecohHalfSolverSpec half)
    (hR : ∀ z, R z ≠ 0 → z ∈ U)
    (hp : ∀ i, (p i).Prime)
    (hζ : ∀ i, IsPrimitiveRoot (ζ i) ((p i) ^ (k i + 1)))
    (hred : ∀ i, RecohCoefficientsReduced (p i) (k i) (obsTerms i))
    (henc : ∀ i B, ((enc i B).map ((ζ i) ^ ·)).sum = recohSupportProbe (bank i) B)
    (hobs : ∀ i, recohCoefficientValue (ζ i) (obsTerms i) = obs i)
    (hcoord : ∀ (u : H₂) (j : J),
      bank (index j) (u : G) = if e u j = 0 then 1 else -1)
    (hnonzero : ∀ j (B : Finset G), B.card = 3 →
      recohSupportProbe (bank (index j)) B ≠ 0) :
    recohCoefficientBackendDecoder U R half index e p k enc obsTerms =
      recohExactDecoder bank (R, obs) := by sorry




end Couret.STROBO2TORS
