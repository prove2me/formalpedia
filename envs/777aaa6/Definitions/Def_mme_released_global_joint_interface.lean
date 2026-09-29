-- Prove2me | Definitions.Def_mme_released_global_joint_interface
-- name    : mme_released_global_joint_interface
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-09-22T15:24:17.973953+00:00
-- url     : https://prove2.me/theorems/cb4e93a8-f46e-4d59-83a0-08bc389402a7
-- title:
--   The physical six-region interface of the exact global candidate
-- statement:
--   Let $B(k)=10^{60}k$. This module restores each published global profile from its hash coordinates to physical coordinates, partitions $24B(k)$ positions into six equal regions, and defines their joint window by imposing the six regional predicates on their respective positions. It also defines the strict usable rates $\rho_o=f_o-10^{-8}$ and assembles the six global Parts with one logarithmic recipe on their entire interface into a GlobalCW.Start. The definitions store no tensor-restriction or numerical-budget assumptions; those are established in separate theorems.
-- source:
--   Auxiliary formalization for Alman et al., More Asymmetry Yields Faster Matrix Multiplication, https://arxiv.org/html/2404.16349v2, Theorem 5.3, Section 5.1, Theorem 6.4 and Algorithm 1. Specialization to the published exact ReleasedGlobal seed; the numerical recursive continuation remains an explicit separate obligation.

import Definitions.Def_mme_released_global_frame_data
import Definitions.Def_mme_global_CW_joint_start_data
import Definitions.Def_mme_released_global_x_certificate
open BigOperators MME MME.ProfiledCW MME.GlobalCW MME.RegionRealization
set_option autoImplicit false
namespace MME.ReleasedGlobal

/-- The hash coordinate corresponding to a physical coordinate. This is the
inverse of the already published `roles` table. -/
def hashMode : Fin 6 → Fin 3 → Fin 3 :=
  ![id, fun i ↦ cyclicPerm.symm (swapFirstTwoPerm.symm i),
    swapFirstTwoPerm.symm, cyclicPerm.symm,
    fun i ↦ cyclicPerm.symm (cyclicPerm.symm i),
    fun i ↦ swapFirstTwoPerm.symm (cyclicPerm.symm i)]

def physicalPredicate {M : ℕ} (o : Fin 6) (P : Predicate M) : Predicate M :=
  fun i ↦ P (hashMode o i)

/-- Restore physical coordinates using the actual symmetry constructors. -/
noncomputable def physicalPart {M ell : ℕ} {P : Predicate M}
    (o : Fin 6) (S : Part M ell P) : Part M ell (physicalPredicate o P) :=
  match o with
  | ⟨0, _⟩ => S
  | ⟨1, _⟩ => S.rotate.swap
  | ⟨2, _⟩ => S.swap
  | ⟨3, _⟩ => S.rotate
  | ⟨4, _⟩ => S.rotate.rotate
  | ⟨5, _⟩ => S.swap.rotate
  | ⟨n + 6, h⟩ => False.elim (by omega)

/-- Six equal global regions, each consisting of four times the block count. -/
def jointPositions (k : ℕ) :
    ((o : Fin 6) × Fin (4 * blocks k)) ≃ Fin (4 * (6 * blocks k)) :=
  (Equiv.sigmaEquivProd _ _).trans
    (finProdFinEquiv.trans (finCongr (by omega)))

noncomputable def physicalWindow (o : Fin 6) (k : ℕ) (hk : 0 < k)
    (a : Reference o k) (eps : ℝ) : Predicate (4 * blocks k) :=
  physicalPredicate o ((frame o k hk a).window (windowGood o k eps))

/-- The entire physical interface passed to a single recursive continuation. -/
noncomputable def jointWindow (k : ℕ) (hk : 0 < k)
    (a : ∀ o : Fin 6, Reference o k) (eps : Fin 6 → ℝ) :
    Predicate (4 * (6 * blocks k)) :=
  fun i x ↦ ∀ o, physicalWindow o k hk (a o) (eps o) i
    (fun r ↦ x (jointPositions k ⟨o,r⟩))

/-- A strict interior rate, with an explicit 10^-8 reserve per block. -/
noncomputable def usableRate (o : Fin 6) : ℝ :=
  (ReleasedGlobalNumeric.rateFloor o : ℝ) - 1 / 100000000

/-- Assemble the six global Parts and one whole-interface continuation. -/
noncomputable def jointStart (k : ℕ) (hk : 0 < k)
    (a : ∀ o : Fin 6, Reference o k) (eps : Fin 6 → ℝ)
    (S : ∀ o, Part (4 * blocks k) 3 (physicalWindow o k hk (a o) (eps o)))
    (R : LogJointRecipe (4 * (6 * blocks k)) 3 (jointWindow k hk a eps)) :
    Start (4 * (6 * blocks k)) 3 where
  parts := 6
  size := fun _ ↦ 4 * blocks k
  positions := jointPositions k
  T := fun o ↦ physicalWindow o k hk (a o) (eps o)
  steps := S
  Q := jointWindow k hk a eps
  target := fun _ _ h ↦ h
  next := R

end MME.ReleasedGlobal


