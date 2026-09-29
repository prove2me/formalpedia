-- Prove2me | Definitions.Def_mme_global_CW_stage_data
-- name    : mme_global_CW_stage_data
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-09-22T07:09:28.475981+00:00
-- url     : https://prove2.me/theorems/ac01b6f1-26c2-409d-bad5-6b591ab3c07f
-- title:
--   Unpaired global CW addresses, compatibility holes, and finite stage data
-- statement:
--   Finite global CW stages on unpaired original blocks. The hash alphabet is a constant-sum simplex with optional coordinate bounds, with no paired-parent grade condition. The data supplies exact fine profiles, target types, actual compatibility-hole counts and finite repair capacity; it does not supply any tensor restriction. Taking one block region and all coordinate bounds equal to the degree gives the unrestricted global simplex.
-- source:
--   More Asymmetry Proposition 5.1 / Theorem 5.3: finite global extraction interface.

import Definitions.Def_mme_hash_extraction_certificate
import Definitions.Def_mme_recursive_yz_CW_cells
import Definitions.Def_mme_recursive_yz_owned_filters
import Definitions.Def_mme_recursive_profiled_CW_data
open BigOperators MME MME.RecursiveYZ MME.CompleteSplit
open scoped Classical
set_option autoImplicit false
namespace MME.GlobalCW

/-- Unpaired original block positions. Unlike recursive child positions, these
have no left/right coordinate and impose no fixed paired-parent type. -/
abbrev Place {R : ℕ} (n : Fin R → ℕ) := (r : Fin R) × Fin (n r)

/-- The existing hash alphabet is used only as a bounded constant-sum simplex.
For a global stage take one region and all bounds equal to degree; then it is
exactly the full simplex of nonnegative triples summing to degree. -/
def cell {degree R : ℕ} {bounds : Fin R → Fin 3 → ℕ} {n : Fin R → ℕ}
    (a : RecursiveXHash.Address degree R bounds n) (p : Place n) : Cell degree R bounds :=
  ⟨p.1,a p.1 p.2⟩

def Graded {degree R ell : ℕ} {bounds : Fin R → Fin 3 → ℕ} {n : Fin R → ℕ}
    (i : Fin 3) (a : RecursiveXHash.Address degree R bounds n)
    (f : Place n → CompleteWord ell) : Prop :=
  ∀ p, CWCells.grade (f p) = ((cell a p).2.val i).val

noncomputable def words {degree R ell : ℕ} {bounds : Fin R → Fin 3 → ℕ} {n : Fin R → ℕ}
    (i : Fin 3) (a : RecursiveXHash.Address degree R bounds n)
    (mu : Cell degree R bounds → CompleteWord ell → ℕ) : Finset (Place n → CompleteWord ell) :=
  Finset.univ.filter (fun f ↦ Graded i a f ∧ Useful (cell a) mu f)

/-- Mode-wise ownership among selected global addresses. The competing address
must share the same physical mode block, as in global asymmetric hashing. -/
noncomputable def Owned {degree R ell k : ℕ} {bounds : Fin R → Fin 3 → ℕ} {n : Fin R → ℕ}
    (address : Fin k → RecursiveXHash.Address degree R bounds n)
    (mu : Fin 3 → Cell degree R bounds → CompleteWord ell → ℕ)
    (j : Fin k) (i : Fin 3) (f : Place n → CompleteWord ell) : Prop :=
  Graded i (address j) f ∧ Useful (cell (address j)) (mu i) f ∧
    (i = 1 → ∀ j', RecursiveXHash.block 1 (address j') = RecursiveXHash.block 1 (address j) →
      Compatible (cell (address j')) yBoundary (modeGroup 1) (mu 1) f → j' = j) ∧
    (i = 2 → ∀ j', RecursiveXHash.block 2 (address j') = RecursiveXHash.block 2 (address j) →
      Compatible (cell (address j')) zBoundary (modeGroup 2) (mu 2) f → j' = j)

/-- Explicit global compatibility holes, counted before choosing an isolated
subfamily. All competitors are target addresses retained by the same hash. -/
noncomputable def holes {degree R ell N p : ℕ} {bounds : Fin R → Fin 3 → ℕ} {n : Fin R → ℕ}
    (m : ∀ r, RecursiveThinSplit.Split degree (bounds r) → ℕ)
    (e : Fin (N+1) ≃ Place n) (S : Finset (ZMod p))
    (state : (Fin (N+2) → ZMod p) × ZMod p)
    (mu : Fin 3 → Cell degree R bounds → CompleteWord ell → ℕ)
    (a : RecursiveXHash.Address degree R bounds n) (i : Fin 3) : Finset (Place n → CompleteWord ell) :=
  (words i a (mu i)).filter fun f ↦
    (i = 1 ∧ ∃ b, b ∈ RecursiveXHash.target m ∧ b ∈ RecursiveXHash.bucketed m e S state ∧
      b ≠ a ∧ RecursiveXHash.block 1 b = RecursiveXHash.block 1 a ∧
      Compatible (cell b) yBoundary (modeGroup 1) (mu 1) f) ∨
    (i = 2 ∧ ∃ b, b ∈ RecursiveXHash.target m ∧ b ∈ RecursiveXHash.bucketed m e S state ∧
      b ≠ a ∧ RecursiveXHash.block 2 b = RecursiveXHash.block 2 a ∧
      Compatible (cell b) zBoundary (modeGroup 2) (mu 2) f)

/-- An exact global stage is finite combinatorial data, never an extraction map.
The degree equality describes one original block, not a pair of parent halves. -/
structure ExactStage (ell M : ℕ) where
  hash : HashExtraction.HashData
  degree_eq : hash.half = 2 * 2 ^ (ell - 1)
  L : ℕ
  positions : Fin L ≃ Place hash.n
  length : L * 2 ^ (ell - 1) = M
  mu : Fin 3 → Cell hash.half hash.R hash.parent → CompleteWord ell → ℕ
  boundary : BoundaryProfiles mu
  reference : hash.Edge
  reference_target : reference ∈ RecursiveXHash.target hash.m
  repairScale : ℕ
  repairExponent : ℕ
  capacity : (∏ i : Fin 3, Nat.card (CWCells.Block ell (cell reference)
    (fun c i ↦ (c.2.val i).val) mu i)) < repairScale ^ repairExponent
  good_holes : ∀ state a, a ∈ hash.good state → ∀ i,
    4 * repairScale * (holes hash.m hash.positions
      (hash.labels.image (fun a : ℕ ↦ (a : ZMod hash.p))) state mu a i).card ≤
        (words i a (mu i)).card

noncomputable def ExactStage.output {ell M : ℕ} (D : ExactStage ell M) : ProfiledCW.Predicate M :=
  fun i x ↦ Graded i D.reference (ProfiledCW.split D.positions D.length x) ∧
    Useful (cell D.reference) (D.mu i) (ProfiledCW.split D.positions D.length x)

noncomputable def ExactStage.copies {ell M : ℕ} (D : ExactStage ell M) : ℕ :=
  ⌈D.hash.lower⌉₊ / 8 ^ D.repairExponent

end MME.GlobalCW


