-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_torsion_subgroup_nsmul
-- name    : Couret.STROBO2TORS.recoh_torsion_subgroup_nsmul
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:49:27.282389+00:00
-- url     : https://prove2.me/theorems/70aeb507-2108-492e-8c79-72019808f11c
-- title:
--   Every torsion-subgroup element is annihilated
-- statement:
--   Let $G$ be an abelian group, $H=G[2]$, $K=G[3]$, and $P_\chi(S)=\sum_{x\in S}\chi(x)$ for a complex additive character $\chi$ (so $\chi(x+y)=\chi(x)\chi(y)$). Write $Q_S$ for ordered-sum counts and $\mathcal O_B(S)=(Q_S,(P_{\chi_i}(S))_i)$ for a bank $B=(\chi_i)$. For every natural $p$ and $x\in G[p]$, $$px=0$$ as an equality inside the subgroup itself. The natural $p=0$ is allowed.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohPrimaryCharacters.lean, lines 43–46; source file SHA-256 aac0eb1afaa745a9c06971d4d58da34eac3567a8d188e887ea7a48d1d5932cfb; theorem Couret.STROBO2TORS.recoh_torsion_subgroup_nsmul

import Definitions.Def_Couret_RecohPrimaryCharacters_3b850762e03a
import Mathlib.Algebra.Module.ZMod
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.Algebra.Module.ZMod
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.FiniteAbelian.Duality

set_option autoImplicit false

/-!
Primary complex character banks for finite abelian groups.

The construction takes coordinates on the subgroup killed by a prime p,
extends their standard complex characters to G, then raises each extension
to the factor of |G| coprime to p.  This gives p-primary characters without
assuming that G itself has exponent p.  All existence statements below are
proved from group structure and cardinality; separation is a conclusion.
-/

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G]

theorem recoh_torsion_subgroup_nsmul (p : ℕ)
    (x : recohTorsionSubgroup (G := G) p) : p • x = 0 := by sorry




variable [Fintype G]

















end Couret.STROBO2TORS
