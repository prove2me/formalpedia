-- Prove2me | Theorems.Thm_mme_complete_split_112_exact_address_MM_dimensions
-- name    : mme_complete_split_112_exact_address_MM_dimensions
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-06T22:38:01.464713+00:00
-- url     : https://prove2.me/theorems/a44593db-0f56-484f-bec8-bad29bf4d3a7
-- title:
--   Exact three matrix-multiplication dimensions of each concrete coupled112 address block
-- statement:
--   For every field K, every nonnegative integer q, and every exact supported coupled address of length 2N with third-mode counts L,L,2G, its block in the literal concrete coupled112 grading is isomorphic to the matrix-multiplication tensor with dimensions (q^(2G),q^(2L),q^(2G)). This strengthens the existing existential matrix-multiplication component certificate by exposing each dimension, rather than only their product q^(4G+2L). The low address types000 and111 each contribute a block of dimensions(1,q,1), while the high types012 and102 contribute(q,1,q). It is a statement about an actual ordered address block of the fixed grading, not an assumption about tensor value or a conclusion about merging different shared-Z components.
-- source:
--   Exact finite tensor-product dimension calculation for the coupled constituent and balanced address profile on Coppersmith and Winograd, Matrix Multiplication via Arithmetic Progressions, J.Symbolic Computation9(1990), journal p.270, https://doi.org/10.1016/S0747-7171(08)80013-2, and the enhanced112 construction of Duan, Wu and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section6.3, https://arxiv.org/abs/2210.10173. This formal refinement computes the same three products already used inside the proof of the existing exact-address common-volume certificate, using the now-public literal coupled grading and four block isomorphisms. It is not asserted to be a separately numbered theorem in those sources.

import Definitions.Def_mme_complete_split_112_coupled_grading_data
import Definitions.Def_mme_CW_q6_primary_hash_family
import Definitions.Def_mme_induced_word_zeroing

open MME MME.CompleteSplit112 BigOperators

universe u

set_option autoImplicit false

theorem mme_complete_split_112_exact_address_MM_dimensions
    {K : Type u} [Field K] (q N L G : ℕ)
    (address : CWQ6ExactCoupledAddress N L G) :
    TensorObj.Isomorphic
      (MMObj K (q ^ (2 * G)) (q ^ (2 * L)) (q ^ (2 * G)))
      (gradedAddressBlock (grading K q) address.1) := by sorry
