-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_parity_coefficient_backend_eq_exact
-- name    : Couret.STROBO2TORS.recoh_parity_coefficient_backend_eq_exact
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:58:26.279886+00:00
-- url     : https://prove2.me/theorems/77bb009f-7f37-4032-aaf5-02cdd031df0d
-- title:
--   The parity coefficient backend equals exact decoding
-- statement:
--   Let $G$ be a finite abelian group. For a character $\chi:G\to\mathbb C$ write $P_\chi(S)=\sum_{x\in S}\chi(x)$, and for a bank $(\chi_i)$ write $\operatorname{Obs}(S)=(Q_S,(P_{\chi_i}(S))_i)$, where $Q_S(z)$ counts ordered pairs from $S$ summing to $z$. The exact decoder of $(R,o)$ consists of all three-element supports $S$ with $\operatorname{Obs}(S)=(R,o)$. Let $I$ be a finite measurement index set and $J$ any coordinate index set. Let $e:G[2]\cong\mathbb F_2^J$ be additive and let $\iota:J\to I$. Let $U\subseteq G$, $R:G\to\mathbb N$, and suppose $R(z)\ne0$ implies $z\in U$. A halving function is sound when every returned $\sigma$ satisfies $2\sigma=t$, and complete when it returns some half whenever one exists. For every $i$, let $p_i$ be prime, $k_i\in\mathbb N$, and $\zeta_i$ primitive of order $p_i^{k_i+1}$. Let a support encoding $E_i(B)$ satisfy $\sum_{a\in E_i(B)}\zeta_i^a=P_{\chi_i}(B)$ for every finite $B$, and let a sparse coefficient list $T_i$ have exponents below $(p_i-1)p_i^{k_i}$ and value $o_i=\sum_{(a,c)\in T_i}c\zeta_i^a$. Assume $\chi_{\iota(j)}(u)=(-1)^{e(u)_j}$ for $u\in G[2]$, and $P_{\chi_{\iota(j)}}(B)\ne0$ for every three-set $B$ and $j\in J$. For a sound and complete halving function, the parity representative backend followed by indexed coefficient-sign recovery and final observation filtering satisfies
--
--   $$\operatorname{ParityCoefficientBackend}(U,R,h,\iota,e,p,k,E,T)=\operatorname{ExactDecoder}(R,o).$$
--
--   Thus the parity candidate reduction preserves the complete semantic solution set.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohParityDecoder.lean, lines 112–145; source file SHA-256 9726528ae3811835f453edf79765026c8ce160b6454c01ab77b6971e40840b98; theorem Couret.STROBO2TORS.recoh_parity_coefficient_backend_eq_exact

import Aesop
import Definitions.Def_Couret_RecohParityDecoder_e5701300ff06
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Module.ZMod
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finite.Card
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_recoh_coefficient_observation_check_iff
import Theorems.Thm_Couret_STROBO2TORS_recoh_coefficient_sign_bools_exact
import Theorems.Thm_Couret_STROBO2TORS_recoh_indexed_boolean_recovery_spec
import Theorems.Thm_Couret_STROBO2TORS_recoh_representative_checked_decoder_eq_exact
import Definitions.Def_Couret_RecohSelectedDecoder_a1594570d3fe
import Definitions.Def_Couret_RecohParityOrbitRefinement_49bc5e3f0a8c
import Definitions.Def_Couret_RecohParitySelector_0eb69704c517

set_option autoImplicit false

/-!
Coefficient decoding from the compact parity family.

The generic bridge uses a proved cover modulo two-torsion, the historical
sign-recovery specification and the exact integer observation checker.
The new candidate construction is an image of the parity family, not the
historical edge-triple enumeration. Definitions enumerate neither G nor
its two-torsion subgroup. Complex values occur only in the specification.
-/

namespace Couret.STROBO2TORS

variable {G I J : Type*} [AddCommGroup G] [DecidableEq G]

local notation "H₂" => recohTorsionSubgroup (G := G) 2













variable [Fintype I]

theorem recoh_parity_coefficient_backend_eq_exact [Fintype G]
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
    recohParityCoefficientBackendDecoder U R half index e p k enc obsTerms =
      recohExactDecoder bank (R, obs) := by sorry


section CyclicSelected

open scoped BigOperators

variable {d : ℕ} (q : Fin d → ℕ) [∀ i, NeZero (q i)]





































































end CyclicSelected

end Couret.STROBO2TORS
