-- Prove2me | Definitions.Def_mme_recursive_yz_stage_certificate
-- name    : mme_recursive_yz_stage_certificate
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-09-12T11:21:50.125985+00:00
-- url     : https://prove2.me/theorems/11babace-1beb-47dd-83df-a4a20a9a1c14
-- title:
--   Concrete recursive Y/Z stages and remaining intact-template assembly
-- statement:
--   A stage attaches concrete CW cell-profile data to a physical recursive hash: both-half positions, boundary-compatible exact profiles, a reference target address, the actual Y/Z type filters, and the repair scale and exponent. Its good-address set is exactly the simultaneous Y/Z usable set. The stage budget records the finite X degree, initial-filter, and compatibility-to-parent-type inequalities.
--
--   The remaining recursive assembly obligation has two explicit parts: embedding the tensor product of literal CW stage sources into the campaign source, and obtaining the required matrix-multiplication direct sum from products of intact cell-profile templates. For input counts $k_j$, each factor contains precisely $\lfloor k_j/8^{h_j}\rfloor$ repaired copies. Thus this obligation begins after concrete extraction and repair; it contains no hypothesis asserting those operations.
-- source:
--   Finite cell-profile formulation of the common-position shuffles used in the Hole Lemma application of Alman et al., More Asymmetry Yields Faster Matrix Multiplication, arXiv:2404.16349v2, Section 6.5; https://arxiv.org/html/2404.16349v2.

import Definitions.Def_mme_hash_extraction_certificate
import Definitions.Def_mme_recursive_yz_CW_cells
import Definitions.Def_mme_recursive_yz_hash_filter
import Definitions.Def_mme_CW_2376_address_block

open BigOperators MME MME.RecursiveYZ MME.CompleteSplit
open scoped Classical
set_option autoImplicit false
universe u
namespace MME.RecursiveYZ.Certificate

/-- Concrete recursive Y/Z data attached to an existing physical hash. -/
structure Stage (D : HashExtraction.HashData) where
  ell : ℕ
  L : ℕ
  repairScale : ℕ
  repairExponent : ℕ
  total : ∀ r, D.parent r 0 + D.parent r 1 + D.parent r 2 = 2 * D.half
  half_eq : D.half = 2 * 2 ^ (ell - 1)
  positions : Fin L ≃ Position D.n
  mu : Fin 3 → Cell D.half D.R D.parent → CompleteWord ell → ℕ
  boundary : BoundaryProfiles mu
  mass : ∀ i c, ∑ w, mu i c w = D.m c.1 c.2 + D.m c.1 (complement (total c.1) c.2)
  reference : D.Edge
  reference_target : reference ∈ RecursiveXHash.target D.m
  keep : Fin 2 → D.Edge → (Position D.n → CompleteWord ell) → Prop
  good_eq : ∀ state, D.good state = usable total D.m D.positions
    (D.labels.image (fun a : ℕ ↦ (a : ZMod D.p))) state repairScale (fun i ↦ mu (yzMode i)) keep
  capacity : (∏ i : Fin 3, Nat.card (CWCells.Block ell (fullCell total reference)
    (fun c i ↦ (c.2.val i).val) mu i)) < repairScale ^ repairExponent

noncomputable def Stage.raw {D : HashExtraction.HashData} (A : Stage D)
    (K : Type u) [Field K] : TensorObj K 3 := CWCells.source K 5 A.ell A.L

noncomputable def Stage.template {D : HashExtraction.HashData} (A : Stage D)
    (K : Type u) [Field K] : TensorObj K 3 :=
  CWCells.unbroken K 5 A.ell A.L A.positions (fullCell A.total A.reference)
    (fun c i ↦ (c.2.val i).val) A.mu

/-- Concrete finite initial-filter and compatibility budgets, before selecting the hash state. -/
noncomputable def Stage.Budget {D : HashExtraction.HashData} (A : Stage D) : Prop :=
  (8 * (RecursiveXHash.ambient (n := D.n) D.m).card ≤
    D.p * ((RecursiveXHash.ambient (n := D.n) D.m).image (RecursiveXHash.block 0)).card) ∧
  (∀ i a, a ∈ RecursiveXHash.target D.m →
    8 * A.repairScale * (typeHoles A.total (yzMode i) a (A.mu (yzMode i)) (A.keep i a)).card ≤
      (unbrokenWords A.total (yzMode i) a (A.mu (yzMode i))).card) ∧
  ∀ i a, a ∈ RecursiveXHash.target D.m →
    ∀ f ∈ unbrokenWords A.total (yzMode i) a (A.mu (yzMode i)), A.keep i a f →
      128 * A.repairScale * ((RecursiveXHash.target (n := D.n) D.m).filter (fun b ↦
        RecursiveXHash.block (yzMode i) b = RecursiveXHash.block (yzMode i) a)).card *
          compatibilityNumber (yzBoundary i) (modeGroup (yzMode i)) (A.mu (yzMode i)) ≤
        D.p * Nat.card {g : Position D.n → CompleteWord A.ell //
          ParentType (RecursiveXHash.block (yzMode i) a)
            (parentCounts (RecursiveXHash.block (yzMode i) a) f) g}

/-- Remaining algebra after the complete Y/Z extraction-and-repair stage.
The first condition embeds the literal CW sources. The second assembles matrix multiplication
from intact cell-profile templates, preserving exact integer copy counts. -/
noncomputable def RecursiveAssembly (D : HashExtraction.Data)
    (A : ∀ j, Stage (D.hash j)) (K : Type u) [Field K] : Prop :=
  TensorObj.Restrict (TensorObj.kronFin D.factors (fun j ↦ (A j).raw K))
    ((sixSymmetrization (StothersFourth.cwFourthObj K 5)).kronPow D.power) ∧
  ∀ counts : Fin D.factors → ℕ,
    (∀ j, (D.hash j).lower ≤ (counts j : ℝ)) →
    TensorObj.Restrict
      (TensorObj.bigAdd (fun _ : Fin ((∏ j, counts j) / D.repairCopies) ↦ MMObj K D.a D.b D.c))
      (TensorObj.kronFin D.factors (fun j ↦
        TensorObj.bigAdd (fun _ : Fin (counts j / 8 ^ (A j).repairExponent) ↦ (A j).template K)))

end MME.RecursiveYZ.Certificate


