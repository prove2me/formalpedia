-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_cyclic_param_fibre_selected_separator
-- name    : Couret.STROBO2TORS.recoh_cyclic_param_fibre_selected_separator
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:55:44.967028+00:00
-- url     : https://prove2.me/theorems/f36a8aba-d2a9-477f-a6a2-b0d9ba79594e
-- title:
--   One selected ternary coordinate separates the two exceptional orbits
-- statement:
--   Let $d\in\mathbb N$ and let $q_0,\ldots,q_{d-1}$ be positive natural moduli. Put $G=\prod_{j<d}\mathbb Z/q_j\mathbb Z$. The primary-$p$ coordinate bank uses the standard character at the full $p$-power factor of each modulus divisible by $p$, with supplied factorization $q_j=p^{k_j+1}c_j$ and $\gcd(p,c_j)=1$. Take supplied primary-three factor data and $a,t,v\in G$ with $t\ne0$, $2t=0$, $v\ne0$, and $3v=0$ (both additive and scalar forms are supplied). Let $i$ be the specified ternary coordinate selected from $v$. For $B,C$ in the full square fibre of $\{a,a+v,a+v+t\}$,
--
--   $$P_{\chi_i}(B)=P_{\chi_i}(C)\Longrightarrow\exists u,\ 2u=0\land C=B+u.$$
--
--   Thus that single coordinate determines which ordinary translation orbit contains a fibre member.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohTernaryFibreSelector.lean, lines 43–90; source file SHA-256 a19004cdbc2c8dfeac9a2b85c2dced7eb2ccc647c2d5a1cbe660309ae6612e56; theorem Couret.STROBO2TORS.recoh_cyclic_param_fibre_selected_separator

import Aesop
import Definitions.Def_Couret_RecohTernaryFibreSelector_4c0db0f29983
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
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
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_recoh_ordinary_partner_of_common_torsion_orbit
import Theorems.Thm_Couret_STROBO2TORS_recoh_param_square_fibre_eq
import Theorems.Thm_Couret_STROBO2TORS_recoh_probe_constant_on_torsion_orbit
import Theorems.Thm_Couret_STROBO2TORS_recoh_ternary_selected_detects
import Theorems.Thm_Couret_STROBO2TORS_recoh_third_probe_separates_exceptional
import Definitions.Def_Couret_RecohTernarySelector_13a2b1134dfc
import Definitions.Def_Couret_RecohOptimalBank_e8b60aaa0883

set_option autoImplicit false

/-!
A single concrete ternary coordinate separates the two translation orbits
of any exceptional triple fibre in a product of cyclic groups. The witness
comes from the executable direction selector. The conclusion quantifies over
the entire fibre, so the later square-only search may use any complete set
of orbit representatives rather than knowing the hidden support.
-/

namespace Couret.STROBO2TORS



variable {d : ℕ} (q : Fin d → ℕ) [∀ i, NeZero (q i)]

theorem recoh_cyclic_param_fibre_selected_separator
    (data3 : RecohPrimaryFactorData q 3)
    (a t v : (j : Fin d) → ZMod (q j))
    (ht : t + t = 0) (ht0 : t ≠ 0)
    (hv : (v + v) + v = 0) (hv0 : v ≠ 0)
    (hvn : 3 • v = 0)
    (B C : Finset ((j : Fin d) → ZMod (q j)))
    (hB : B ∈ squareFibre (paramSupport ((a, t), v)))
    (hC : C ∈ squareFibre (paramSupport ((a, t), v)))
    (heq :
      recohSupportProbe
        (recohCyclicPrimaryBank q 3 data3 (recohTernaryCoordinate q v hvn hv0)) B =
      recohSupportProbe
        (recohCyclicPrimaryBank q 3 data3 (recohTernaryCoordinate q v hvn hv0)) C) :
    OrdinaryPartner B C := by sorry




end Couret.STROBO2TORS
