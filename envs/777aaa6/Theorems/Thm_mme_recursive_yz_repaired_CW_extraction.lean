-- Prove2me | Theorems.Thm_mme_recursive_yz_repaired_CW_extraction
-- name    : mme_recursive_yz_repaired_CW_extraction
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-12T11:21:02.347973+00:00
-- url     : https://prove2.me/theorems/dff67224-c202-421f-bdf2-d59d8ca7f1f6
-- title:
--   Actual recursive CW extraction with independent repaired copies and exact repair cost
-- statement:
--   Fix a target recursive split type and a reference address of that type. Let $k$ distinct target addresses survive one physical hash, be X-isolated against the entire retained ambient family, and satisfy the actual Y/Z hole budgets. Assume the three boundary profile identities forced by CW support. If each Y/Z hole set obeys $4d|H|\le |U_i|$ and the product of the reference template block counts is below $d^h$, then the literal CW power restricts to $$\left\lfloor\frac{k}{8^h}\right\rfloor$$ independent copies of its intact reference cell-profile tensor.
--
--   Both halves of every parent occurrence are included. The proof derives ownership from actual CW coefficients and counted nonholes, normalizes each selected copy, and repairs disjoint groups of $8^h$ copies. There is no assumed extraction, ownership, or tensor-symmetry premise.
-- source:
--   Finite recursive extraction in Alman et al., More Asymmetry Yields Faster Matrix Multiplication, arXiv:2404.16349v2, Sections 6.3--6.5; https://arxiv.org/html/2404.16349v2.

import Theorems.Thm_mme_bigAdd_fin_mul_grouped_restrict
import Theorems.Thm_mme_bigAdd_prefix_restrict
import Theorems.Thm_mme_recursive_yz_actual_CW_cell_finite_hole_repair
import Theorems.Thm_mme_recursive_yz_actual_CW_power_extraction
import Theorems.Thm_mme_recursive_yz_same_type_cell_permutation
import Theorems.Thm_mme_recursive_yz_nonhole_implies_owned
import Theorems.Thm_mme_kronPow_position_permutation_linear_equiv
import Definitions.Def_mme_recursive_yz_CW_cells
import Theorems.Thm_mme_restrict_basisAllAllowedSubtensor_of_vanishes
import Definitions.Def_mme_tensor_quotient
import Definitions.Def_mme_TypeGrading_kron
import Definitions.Def_mme_modern_three_mode_projected_tensor
open BigOperators MME MME.TensorObj MME.CompleteSplit MME.RecursiveYZ
  MME.RecursiveYZ.CWCells MME.DWZComponentRestriction MME.ModernRepair Module
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 800000
universe u v w

theorem mme_recursive_yz_repaired_CW_extraction {K : Type u} [Field K] (q ell half R N p L d h k : ℕ)
    (parent : Fin R → Fin 3 → ℕ) (n : Fin R → ℕ)
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (hhalf : half = 2 * 2 ^ (ell - 1))
    (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (e : Fin (N + 1) ≃ (r : Fin R) × Fin (n r)) (positions : Fin L ≃ Position n)
    (S : Finset (ZMod p)) (state : (Fin (N + 2) → ZMod p) × ZMod p)
    (ref : Address half R parent n) (href : ref ∈ RecursiveXHash.target m)
    (address : Fin k → Address half R parent n) (hinj : Function.Injective address)
    (hT : ∀ j, address j ∈ RecursiveXHash.target m)
    (hE : ∀ j, address j ∈ RecursiveXHash.bucketed m e S state)
    (hHash : ∀ j, address j ∈ RecursiveXHash.hashed m e S state)
    (hiso : ∀ j b, b ∈ RecursiveXHash.bucketed m e S state →
      RecursiveXHash.block 0 (address j) = RecursiveXHash.block 0 b → address j = b)
    (mu : Fin 3 → Cell half R parent → CompleteWord ell → ℕ) (hmu : BoundaryProfiles mu)
    (keep : Fin 2 → Fin k → (Position n → CompleteWord ell) → Prop)
    (hholes : ∀ j i, 4 * d * (filterHoles htotal m e S state i (mu (yzMode i))
      (address j) (keep i j)).card ≤ (unbrokenWords htotal (yzMode i) (address j) (mu (yzMode i))).card)
    (hcapacity : (∏ i : Fin 3, Nat.card (Block ell (fullCell htotal ref)
      (fun c i ↦ (c.2.val i).val) mu i)) < d ^ h) :
    Restrict (bigAdd (fun _ : Fin (k / 8 ^ h) ↦
      unbroken K q ell L positions (fullCell htotal ref) (fun c i ↦ (c.2.val i).val) mu))
      (source K q ell L)  := by sorry
